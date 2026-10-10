import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes52
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw6656 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![0, 1, -1], ![2, -1, -1]]
def raw6656Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6656step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -3, 2], ![0, 1, -1], ![2, -1, -1]]
def raw6656step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6656step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw6656step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6656step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw6656step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6656 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6656 raw6656Labels = mixedMoment B node2879 node2879Labels := by
  calc
    mixedMoment B raw6656 raw6656Labels = mixedMoment B raw6656step0 raw6656step0Labels := by
      have hz : ∀ j, raw6656 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6656step0 = (fun i j => raw6656 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6656step0 raw6656; decide +kernel
      have hl : raw6656step0Labels = raw6656Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6656 raw6656Labels permutation346 hz
    mixedMoment B raw6656step0 raw6656step0Labels = mixedMoment B raw6656step1 raw6656step1Labels := by
      have ha : raw6656step1 = (fun i j => raw6656step0 (permutation101 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6656step1 raw6656step0; decide +kernel
      have hl : raw6656step1Labels = raw6656step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6656step0 raw6656step0Labels permutation101 permutation5
    mixedMoment B raw6656step1 raw6656step1Labels = mixedMoment B raw6656step2 raw6656step2Labels := by
      have ha : raw6656step2 = raw6656step1 := by apply Matrix.ext; unfold raw6656step2 raw6656step1; decide +kernel
      have hl : raw6656step1Labels = labelEmbedding1 ∘ raw6656step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6656step1 raw6656step1Labels raw6656step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2879 node2879Labels := by rfl

def raw6657 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1]]
def raw6657Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6657step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1]]
def raw6657step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6657step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw6657step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6657step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw6657step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6657 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6657 raw6657Labels = mixedMoment B node3075 node3075Labels := by
  calc
    mixedMoment B raw6657 raw6657Labels = mixedMoment B raw6657step0 raw6657step0Labels := by
      have hz : ∀ j, raw6657 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6657step0 = (fun i j => raw6657 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6657step0 raw6657; decide +kernel
      have hl : raw6657step0Labels = raw6657Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6657 raw6657Labels permutation346 hz
    mixedMoment B raw6657step0 raw6657step0Labels = mixedMoment B raw6657step1 raw6657step1Labels := by
      have ha : raw6657step1 = (fun i j => raw6657step0 (permutation97 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6657step1 raw6657step0; decide +kernel
      have hl : raw6657step1Labels = raw6657step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6657step0 raw6657step0Labels permutation97 permutation5
    mixedMoment B raw6657step1 raw6657step1Labels = mixedMoment B raw6657step2 raw6657step2Labels := by
      have ha : raw6657step2 = raw6657step1 := by apply Matrix.ext; unfold raw6657step2 raw6657step1; decide +kernel
      have hl : raw6657step1Labels = labelEmbedding1 ∘ raw6657step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6657step1 raw6657step1Labels raw6657step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3075 node3075Labels := by rfl

def raw6658 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![2, -1, -1], ![2, -1, -1]]
def raw6658Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6658step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, -2, 2], ![2, -1, -1], ![2, -1, -1]]
def raw6658step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6658step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw6658step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6658step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def raw6658step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6658step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def raw6658step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6658 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6658 raw6658Labels = mixedMoment B node1626 node1626Labels := by
  calc
    mixedMoment B raw6658 raw6658Labels = mixedMoment B raw6658step0 raw6658step0Labels := by
      have hz : ∀ j, raw6658 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6658step0 = (fun i j => raw6658 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6658step0 raw6658; decide +kernel
      have hl : raw6658step0Labels = raw6658Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6658 raw6658Labels permutation346 hz
    mixedMoment B raw6658step0 raw6658step0Labels = mixedMoment B raw6658step1 raw6658step1Labels := by
      have ha : raw6658step1 = (fun i j => raw6658step0 (permutation35 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6658step1 raw6658step0; decide +kernel
      have hl : raw6658step1Labels = raw6658step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6658step0 raw6658step0Labels permutation35 permutation5
    mixedMoment B raw6658step1 raw6658step1Labels = mixedMoment B raw6658step2 raw6658step2Labels := by
      have ha : raw6658step2 = -raw6658step1 := by apply Matrix.ext; change ∀ i j, raw6658step2 i j = -(raw6658step1 i j); unfold raw6658step2 raw6658step1; decide +kernel
      have hl : raw6658step2Labels = raw6658step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6658step2 raw6658step2Labels = mixedMoment B raw6658step3 raw6658step3Labels := by
      have ha : raw6658step3 = raw6658step2 := by apply Matrix.ext; unfold raw6658step3 raw6658step2; decide +kernel
      have hl : raw6658step2Labels = labelEmbedding1 ∘ raw6658step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6658step2 raw6658step2Labels raw6658step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1626 node1626Labels := by rfl

def raw6659 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, 0, 0], ![0, -2, 2], ![2, -1, -1], ![2, -1, -1]]
def raw6659Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6659step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, -2, 2], ![2, -1, -1], ![2, -1, -1]]
def raw6659step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6659step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![-1, -1, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw6659step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6659step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def raw6659step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6659step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def raw6659step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6659 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6659 raw6659Labels = mixedMoment B node3359 node3359Labels := by
  calc
    mixedMoment B raw6659 raw6659Labels = mixedMoment B raw6659step0 raw6659step0Labels := by
      have hz : ∀ j, raw6659 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6659step0 = (fun i j => raw6659 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6659step0 raw6659; decide +kernel
      have hl : raw6659step0Labels = raw6659Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6659 raw6659Labels permutation346 hz
    mixedMoment B raw6659step0 raw6659step0Labels = mixedMoment B raw6659step1 raw6659step1Labels := by
      have ha : raw6659step1 = (fun i j => raw6659step0 (permutation35 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6659step1 raw6659step0; decide +kernel
      have hl : raw6659step1Labels = raw6659step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6659step0 raw6659step0Labels permutation35 permutation5
    mixedMoment B raw6659step1 raw6659step1Labels = mixedMoment B raw6659step2 raw6659step2Labels := by
      have ha : raw6659step2 = -raw6659step1 := by apply Matrix.ext; change ∀ i j, raw6659step2 i j = -(raw6659step1 i j); unfold raw6659step2 raw6659step1; decide +kernel
      have hl : raw6659step2Labels = raw6659step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6659step2 raw6659step2Labels = mixedMoment B raw6659step3 raw6659step3Labels := by
      have ha : raw6659step3 = raw6659step2 := by apply Matrix.ext; unfold raw6659step3 raw6659step2; decide +kernel
      have hl : raw6659step2Labels = labelEmbedding1 ∘ raw6659step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6659step2 raw6659step2Labels raw6659step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3359 node3359Labels := by rfl

def raw6660 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, 1, 0], ![0, -2, 2], ![2, -1, -1], ![2, -1, -1]]
def raw6660Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6660step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw6660step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6660step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def raw6660step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6660step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def raw6660step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6660 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6660 raw6660Labels = mixedMoment B node3438 node3438Labels := by
  calc
    mixedMoment B raw6660 raw6660Labels = mixedMoment B raw6660step0 raw6660step0Labels := by
      have ha : raw6660step0 = (fun i j => raw6660 (permutation179 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6660step0 raw6660; decide +kernel
      have hl : raw6660step0Labels = raw6660Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6660 raw6660Labels permutation179 permutation5
    mixedMoment B raw6660step0 raw6660step0Labels = mixedMoment B raw6660step1 raw6660step1Labels := by
      have ha : raw6660step1 = -raw6660step0 := by apply Matrix.ext; change ∀ i j, raw6660step1 i j = -(raw6660step0 i j); unfold raw6660step1 raw6660step0; decide +kernel
      have hl : raw6660step1Labels = raw6660step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6660step1 raw6660step1Labels = mixedMoment B raw6660step2 raw6660step2Labels := by
      have ha : raw6660step2 = raw6660step1 := by apply Matrix.ext; unfold raw6660step2 raw6660step1; decide +kernel
      have hl : raw6660step1Labels = labelEmbedding1 ∘ raw6660step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6660step1 raw6660step1Labels raw6660step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3438 node3438Labels := by rfl

def raw6661 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![-1, -1, 2], ![2, -1, -1], ![2, -1, -1]]
def raw6661Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6661step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, -1, 2], ![2, -1, -1], ![2, -1, -1]]
def raw6661step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6661step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 2, -1], ![-1, -1, 2], ![-1, -1, 2]]
def raw6661step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6661step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw6661step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6661step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw6661step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6661 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6661 raw6661Labels = mixedMoment B node3542 node3542Labels := by
  calc
    mixedMoment B raw6661 raw6661Labels = mixedMoment B raw6661step0 raw6661step0Labels := by
      have hz : ∀ j, raw6661 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6661step0 = (fun i j => raw6661 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6661step0 raw6661; decide +kernel
      have hl : raw6661step0Labels = raw6661Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6661 raw6661Labels permutation346 hz
    mixedMoment B raw6661step0 raw6661step0Labels = mixedMoment B raw6661step1 raw6661step1Labels := by
      have ha : raw6661step1 = (fun i j => raw6661step0 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6661step1 raw6661step0; decide +kernel
      have hl : raw6661step1Labels = raw6661step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6661step0 raw6661step0Labels permutation32 permutation5
    mixedMoment B raw6661step1 raw6661step1Labels = mixedMoment B raw6661step2 raw6661step2Labels := by
      have ha : raw6661step2 = -raw6661step1 := by apply Matrix.ext; change ∀ i j, raw6661step2 i j = -(raw6661step1 i j); unfold raw6661step2 raw6661step1; decide +kernel
      have hl : raw6661step2Labels = raw6661step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6661step2 raw6661step2Labels = mixedMoment B raw6661step3 raw6661step3Labels := by
      have ha : raw6661step3 = raw6661step2 := by apply Matrix.ext; unfold raw6661step3 raw6661step2; decide +kernel
      have hl : raw6661step2Labels = labelEmbedding1 ∘ raw6661step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6661step2 raw6661step2Labels raw6661step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3542 node3542Labels := by rfl

def raw6662 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![2, -1, -1], ![1, 0, -1]]
def raw6662Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6662step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -2, 2], ![2, -1, -1], ![1, 0, -1]]
def raw6662step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6662step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw6662step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6662step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6662step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6662step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6662step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6662 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6662 raw6662Labels = mixedMoment B node3535 node3535Labels := by
  calc
    mixedMoment B raw6662 raw6662Labels = mixedMoment B raw6662step0 raw6662step0Labels := by
      have hz : ∀ j, raw6662 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6662step0 = (fun i j => raw6662 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6662step0 raw6662; decide +kernel
      have hl : raw6662step0Labels = raw6662Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6662 raw6662Labels permutation346 hz
    mixedMoment B raw6662step0 raw6662step0Labels = mixedMoment B raw6662step1 raw6662step1Labels := by
      have ha : raw6662step1 = (fun i j => raw6662step0 (permutation37 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6662step1 raw6662step0; decide +kernel
      have hl : raw6662step1Labels = raw6662step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6662step0 raw6662step0Labels permutation37 permutation5
    mixedMoment B raw6662step1 raw6662step1Labels = mixedMoment B raw6662step2 raw6662step2Labels := by
      have ha : raw6662step2 = -raw6662step1 := by apply Matrix.ext; change ∀ i j, raw6662step2 i j = -(raw6662step1 i j); unfold raw6662step2 raw6662step1; decide +kernel
      have hl : raw6662step2Labels = raw6662step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6662step2 raw6662step2Labels = mixedMoment B raw6662step3 raw6662step3Labels := by
      have ha : raw6662step3 = raw6662step2 := by apply Matrix.ext; unfold raw6662step3 raw6662step2; decide +kernel
      have hl : raw6662step2Labels = labelEmbedding1 ∘ raw6662step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6662step2 raw6662step2Labels raw6662step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3535 node3535Labels := by rfl

def raw6663 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![3, -2, -1]]
def raw6663Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6663step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, -2, 2], ![1, 0, -1], ![3, -2, -1]]
def raw6663step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6663step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -1, 1], ![-2, 2, 0], ![-2, -1, 3]]
def raw6663step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6663step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw6663step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6663step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw6663step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6663 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6663 raw6663Labels = mixedMoment B node1604 node1604Labels := by
  calc
    mixedMoment B raw6663 raw6663Labels = mixedMoment B raw6663step0 raw6663step0Labels := by
      have hz : ∀ j, raw6663 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6663step0 = (fun i j => raw6663 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6663step0 raw6663; decide +kernel
      have hl : raw6663step0Labels = raw6663Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6663 raw6663Labels permutation346 hz
    mixedMoment B raw6663step0 raw6663step0Labels = mixedMoment B raw6663step1 raw6663step1Labels := by
      have ha : raw6663step1 = (fun i j => raw6663step0 (permutation34 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6663step1 raw6663step0; decide +kernel
      have hl : raw6663step1Labels = raw6663step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6663step0 raw6663step0Labels permutation34 permutation5
    mixedMoment B raw6663step1 raw6663step1Labels = mixedMoment B raw6663step2 raw6663step2Labels := by
      have ha : raw6663step2 = -raw6663step1 := by apply Matrix.ext; change ∀ i j, raw6663step2 i j = -(raw6663step1 i j); unfold raw6663step2 raw6663step1; decide +kernel
      have hl : raw6663step2Labels = raw6663step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6663step2 raw6663step2Labels = mixedMoment B raw6663step3 raw6663step3Labels := by
      have ha : raw6663step3 = raw6663step2 := by apply Matrix.ext; unfold raw6663step3 raw6663step2; decide +kernel
      have hl : raw6663step2Labels = labelEmbedding1 ∘ raw6663step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6663step2 raw6663step2Labels raw6663step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1604 node1604Labels := by rfl

def raw6664 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![3, -2, -1]]
def raw6664Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6664step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![3, -2, -1]]
def raw6664step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6664step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, -1, 3]]
def raw6664step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6664step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw6664step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6664step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw6664step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6664 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6664 raw6664Labels = mixedMoment B node3343 node3343Labels := by
  calc
    mixedMoment B raw6664 raw6664Labels = mixedMoment B raw6664step0 raw6664step0Labels := by
      have hz : ∀ j, raw6664 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6664step0 = (fun i j => raw6664 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6664step0 raw6664; decide +kernel
      have hl : raw6664step0Labels = raw6664Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6664 raw6664Labels permutation346 hz
    mixedMoment B raw6664step0 raw6664step0Labels = mixedMoment B raw6664step1 raw6664step1Labels := by
      have ha : raw6664step1 = (fun i j => raw6664step0 (permutation34 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6664step1 raw6664step0; decide +kernel
      have hl : raw6664step1Labels = raw6664step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6664step0 raw6664step0Labels permutation34 permutation5
    mixedMoment B raw6664step1 raw6664step1Labels = mixedMoment B raw6664step2 raw6664step2Labels := by
      have ha : raw6664step2 = -raw6664step1 := by apply Matrix.ext; change ∀ i j, raw6664step2 i j = -(raw6664step1 i j); unfold raw6664step2 raw6664step1; decide +kernel
      have hl : raw6664step2Labels = raw6664step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6664step2 raw6664step2Labels = mixedMoment B raw6664step3 raw6664step3Labels := by
      have ha : raw6664step3 = raw6664step2 := by apply Matrix.ext; unfold raw6664step3 raw6664step2; decide +kernel
      have hl : raw6664step2Labels = labelEmbedding1 ∘ raw6664step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6664step2 raw6664step2Labels raw6664step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3343 node3343Labels := by rfl

def raw6665 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![3, -2, -1]]
def raw6665Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6665step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw6665step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6665step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw6665step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6665 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6665 raw6665Labels = mixedMoment B node3368 node3368Labels := by
  calc
    mixedMoment B raw6665 raw6665Labels = mixedMoment B raw6665step0 raw6665step0Labels := by
      have ha : raw6665step0 = (fun i j => raw6665 (permutation662 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6665step0 raw6665; decide +kernel
      have hl : raw6665step0Labels = raw6665Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6665 raw6665Labels permutation662 permutation5
    mixedMoment B raw6665step0 raw6665step0Labels = mixedMoment B raw6665step1 raw6665step1Labels := by
      have ha : raw6665step1 = raw6665step0 := by apply Matrix.ext; unfold raw6665step1 raw6665step0; decide +kernel
      have hl : raw6665step0Labels = labelEmbedding1 ∘ raw6665step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6665step0 raw6665step0Labels raw6665step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3368 node3368Labels := by rfl

def raw6666 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![-1, -1, 2], ![1, 0, -1], ![3, -2, -1]]
def raw6666Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6666step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, -1, 2], ![1, 0, -1], ![3, -2, -1]]
def raw6666step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6666step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-2, -1, 3]]
def raw6666step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6666step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw6666step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6666step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw6666step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6666 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6666 raw6666Labels = mixedMoment B node3530 node3530Labels := by
  calc
    mixedMoment B raw6666 raw6666Labels = mixedMoment B raw6666step0 raw6666step0Labels := by
      have hz : ∀ j, raw6666 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6666step0 = (fun i j => raw6666 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6666step0 raw6666; decide +kernel
      have hl : raw6666step0Labels = raw6666Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6666 raw6666Labels permutation346 hz
    mixedMoment B raw6666step0 raw6666step0Labels = mixedMoment B raw6666step1 raw6666step1Labels := by
      have ha : raw6666step1 = (fun i j => raw6666step0 (permutation34 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6666step1 raw6666step0; decide +kernel
      have hl : raw6666step1Labels = raw6666step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6666step0 raw6666step0Labels permutation34 permutation5
    mixedMoment B raw6666step1 raw6666step1Labels = mixedMoment B raw6666step2 raw6666step2Labels := by
      have ha : raw6666step2 = -raw6666step1 := by apply Matrix.ext; change ∀ i j, raw6666step2 i j = -(raw6666step1 i j); unfold raw6666step2 raw6666step1; decide +kernel
      have hl : raw6666step2Labels = raw6666step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6666step2 raw6666step2Labels = mixedMoment B raw6666step3 raw6666step3Labels := by
      have ha : raw6666step3 = raw6666step2 := by apply Matrix.ext; unfold raw6666step3 raw6666step2; decide +kernel
      have hl : raw6666step2Labels = labelEmbedding1 ∘ raw6666step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6666step2 raw6666step2Labels raw6666step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3530 node3530Labels := by rfl

def raw6667 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![0, 1, -1], ![3, -2, -1]]
def raw6667Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6667step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -2, 2], ![0, 1, -1], ![3, -2, -1]]
def raw6667step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6667step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw6667step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6667step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw6667step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6667 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6667 raw6667Labels = mixedMoment B node3389 node3389Labels := by
  calc
    mixedMoment B raw6667 raw6667Labels = mixedMoment B raw6667step0 raw6667step0Labels := by
      have hz : ∀ j, raw6667 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6667step0 = (fun i j => raw6667 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6667step0 raw6667; decide +kernel
      have hl : raw6667step0Labels = raw6667Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6667 raw6667Labels permutation346 hz
    mixedMoment B raw6667step0 raw6667step0Labels = mixedMoment B raw6667step1 raw6667step1Labels := by
      have ha : raw6667step1 = (fun i j => raw6667step0 (permutation143 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6667step1 raw6667step0; decide +kernel
      have hl : raw6667step1Labels = raw6667step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6667step0 raw6667step0Labels permutation143 permutation5
    mixedMoment B raw6667step1 raw6667step1Labels = mixedMoment B raw6667step2 raw6667step2Labels := by
      have ha : raw6667step2 = raw6667step1 := by apply Matrix.ext; unfold raw6667step2 raw6667step1; decide +kernel
      have hl : raw6667step1Labels = labelEmbedding1 ∘ raw6667step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6667step1 raw6667step1Labels raw6667step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3389 node3389Labels := by rfl

def raw6668 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw6668Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6668step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw6668step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6668step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw6668step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6668 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6668 raw6668Labels = mixedMoment B node3039 node3039Labels := by
  calc
    mixedMoment B raw6668 raw6668Labels = mixedMoment B raw6668step0 raw6668step0Labels := by
      have hz : ∀ j, raw6668 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6668step0 = (fun i j => raw6668 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6668step0 raw6668; decide +kernel
      have hl : raw6668step0Labels = raw6668Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6668 raw6668Labels permutation346 hz
    mixedMoment B raw6668step0 raw6668step0Labels = mixedMoment B raw6668step1 raw6668step1Labels := by
      have ha : raw6668step1 = (fun i j => raw6668step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6668step1 raw6668step0; decide +kernel
      have hl : raw6668step1Labels = raw6668step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6668step0 raw6668step0Labels permutation38 permutation2
    _ = mixedMoment B node3039 node3039Labels := by rfl

def raw6669 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw6669Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6669step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw6669step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6669step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw6669step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6669 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6669 raw6669Labels = mixedMoment B node3881 node3881Labels := by
  calc
    mixedMoment B raw6669 raw6669Labels = mixedMoment B raw6669step0 raw6669step0Labels := by
      have hz : ∀ j, raw6669 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6669step0 = (fun i j => raw6669 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6669step0 raw6669; decide +kernel
      have hl : raw6669step0Labels = raw6669Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6669 raw6669Labels permutation346 hz
    mixedMoment B raw6669step0 raw6669step0Labels = mixedMoment B raw6669step1 raw6669step1Labels := by
      have ha : raw6669step1 = (fun i j => raw6669step0 (permutation102 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6669step1 raw6669step0; decide +kernel
      have hl : raw6669step1Labels = raw6669step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6669step0 raw6669step0Labels permutation102 permutation4
    _ = mixedMoment B node3881 node3881Labels := by rfl

def raw6670 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw6670Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6670step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw6670step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6670 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6670 raw6670Labels = mixedMoment B node3880 node3880Labels := by
  calc
    mixedMoment B raw6670 raw6670Labels = mixedMoment B raw6670step0 raw6670step0Labels := by
      have ha : raw6670step0 = (fun i j => raw6670 (permutation515 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6670step0 raw6670; decide +kernel
      have hl : raw6670step0Labels = raw6670Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6670 raw6670Labels permutation515 permutation4
    _ = mixedMoment B node3880 node3880Labels := by rfl

def raw6671 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1]]
def raw6671Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6671step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1]]
def raw6671step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6671step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw6671step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6671 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6671 raw6671Labels = mixedMoment B node3958 node3958Labels := by
  calc
    mixedMoment B raw6671 raw6671Labels = mixedMoment B raw6671step0 raw6671step0Labels := by
      have hz : ∀ j, raw6671 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6671step0 = (fun i j => raw6671 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6671step0 raw6671; decide +kernel
      have hl : raw6671step0Labels = raw6671Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6671 raw6671Labels permutation346 hz
    mixedMoment B raw6671step0 raw6671step0Labels = mixedMoment B raw6671step1 raw6671step1Labels := by
      have ha : raw6671step1 = (fun i j => raw6671step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6671step1 raw6671step0; decide +kernel
      have hl : raw6671step1Labels = raw6671step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6671step0 raw6671step0Labels permutation38 permutation2
    _ = mixedMoment B node3958 node3958Labels := by rfl

def raw6672 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![0, 1, -1], ![2, -1, -1]]
def raw6672Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6672step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, -2, 2], ![0, 1, -1], ![2, -1, -1]]
def raw6672step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6672step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw6672step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6672 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6672 raw6672Labels = mixedMoment B node3885 node3885Labels := by
  calc
    mixedMoment B raw6672 raw6672Labels = mixedMoment B raw6672step0 raw6672step0Labels := by
      have hz : ∀ j, raw6672 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6672step0 = (fun i j => raw6672 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6672step0 raw6672; decide +kernel
      have hl : raw6672step0Labels = raw6672Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6672 raw6672Labels permutation346 hz
    mixedMoment B raw6672step0 raw6672step0Labels = mixedMoment B raw6672step1 raw6672step1Labels := by
      have ha : raw6672step1 = (fun i j => raw6672step0 (permutation98 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6672step1 raw6672step0; decide +kernel
      have hl : raw6672step1Labels = raw6672step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6672step0 raw6672step0Labels permutation98 permutation4
    _ = mixedMoment B node3885 node3885Labels := by rfl

def raw6673 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1]]
def raw6673Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6673step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1]]
def raw6673step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6673step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw6673step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6673 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6673 raw6673Labels = mixedMoment B node3910 node3910Labels := by
  calc
    mixedMoment B raw6673 raw6673Labels = mixedMoment B raw6673step0 raw6673step0Labels := by
      have hz : ∀ j, raw6673 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6673step0 = (fun i j => raw6673 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6673step0 raw6673; decide +kernel
      have hl : raw6673step0Labels = raw6673Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6673 raw6673Labels permutation346 hz
    mixedMoment B raw6673step0 raw6673step0Labels = mixedMoment B raw6673step1 raw6673step1Labels := by
      have ha : raw6673step1 = (fun i j => raw6673step0 (permutation96 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6673step1 raw6673step0; decide +kernel
      have hl : raw6673step1Labels = raw6673step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6673step0 raw6673step0Labels permutation96 permutation4
    _ = mixedMoment B node3910 node3910Labels := by rfl

def raw6674 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![0, 0], ![-2, 2], ![1, -1], ![1, -1]]
def raw6674Labels : Fin 2 → Fin 2 := ![0, 1]

def raw6674step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![-2, 2], ![1, -1], ![1, -1]]
def raw6674step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw6674step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw6674step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical6674 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6674 raw6674Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw6674 raw6674Labels = mixedMoment B raw6674step0 raw6674step0Labels := by
      have hz : ∀ j, raw6674 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6674step0 = (fun i j => raw6674 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6674step0 raw6674; decide +kernel
      have hl : raw6674step0Labels = raw6674Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6674 raw6674Labels permutation346 hz
    mixedMoment B raw6674step0 raw6674step0Labels = mixedMoment B raw6674step1 raw6674step1Labels := by
      have ha : raw6674step1 = (fun i j => raw6674step0 (permutation80 i) (permutation0 j)) := by apply Matrix.ext; unfold raw6674step1 raw6674step0; decide +kernel
      have hl : raw6674step1Labels = raw6674step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6674step0 raw6674step0Labels permutation80 permutation0
    _ = mixedMoment B node4091 node4091Labels := by rfl

def raw6675 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, 0, -1], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw6675Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6675step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, 0, -1], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw6675step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6675step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw6675step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6675 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6675 raw6675Labels = mixedMoment B node1370 node1370Labels := by
  calc
    mixedMoment B raw6675 raw6675Labels = mixedMoment B raw6675step0 raw6675step0Labels := by
      have hz : ∀ j, raw6675 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6675step0 = (fun i j => raw6675 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6675step0 raw6675; decide +kernel
      have hl : raw6675step0Labels = raw6675Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6675 raw6675Labels permutation346 hz
    mixedMoment B raw6675step0 raw6675step0Labels = mixedMoment B raw6675step1 raw6675step1Labels := by
      have ha : raw6675step1 = (fun i j => raw6675step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6675step1 raw6675step0; decide +kernel
      have hl : raw6675step1Labels = raw6675step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6675step0 raw6675step0Labels permutation38 permutation2
    _ = mixedMoment B node1370 node1370Labels := by rfl

def raw6676 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -1, 0], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw6676Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6676step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw6676step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6676 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6676 raw6676Labels = mixedMoment B node1358 node1358Labels := by
  calc
    mixedMoment B raw6676 raw6676Labels = mixedMoment B raw6676step0 raw6676step0Labels := by
      have ha : raw6676step0 = (fun i j => raw6676 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6676step0 raw6676; decide +kernel
      have hl : raw6676step0Labels = raw6676Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6676 raw6676Labels permutation200 permutation2
    _ = mixedMoment B node1358 node1358Labels := by rfl

def raw6677 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![1, 0, -1], ![2, -1, -1]]
def raw6677Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6677step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![2, -1, -1]]
def raw6677step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6677 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6677 raw6677Labels = mixedMoment B node1423 node1423Labels := by
  calc
    mixedMoment B raw6677 raw6677Labels = mixedMoment B raw6677step0 raw6677step0Labels := by
      have hz : ∀ j, raw6677 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6677step0 = (fun i j => raw6677 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6677step0 raw6677; decide +kernel
      have hl : raw6677step0Labels = raw6677Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6677 raw6677Labels permutation346 hz
    _ = mixedMoment B node1423 node1423Labels := by rfl

def raw6678 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![2, -1, -1], ![2, -1, -1]]
def raw6678Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6678step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, -2, 2], ![2, -1, -1], ![2, -1, -1]]
def raw6678step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6678step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw6678step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6678 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6678 raw6678Labels = mixedMoment B node1363 node1363Labels := by
  calc
    mixedMoment B raw6678 raw6678Labels = mixedMoment B raw6678step0 raw6678step0Labels := by
      have hz : ∀ j, raw6678 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6678step0 = (fun i j => raw6678 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6678step0 raw6678; decide +kernel
      have hl : raw6678step0Labels = raw6678Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6678 raw6678Labels permutation346 hz
    mixedMoment B raw6678step0 raw6678step0Labels = mixedMoment B raw6678step1 raw6678step1Labels := by
      have ha : raw6678step1 = (fun i j => raw6678step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6678step1 raw6678step0; decide +kernel
      have hl : raw6678step1Labels = raw6678step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6678step0 raw6678step0Labels permutation38 permutation2
    _ = mixedMoment B node1363 node1363Labels := by rfl

def raw6679 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![3, -2, -1]]
def raw6679Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6679step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, -2, 2], ![1, 0, -1], ![3, -2, -1]]
def raw6679step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6679step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw6679step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6679 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6679 raw6679Labels = mixedMoment B node1361 node1361Labels := by
  calc
    mixedMoment B raw6679 raw6679Labels = mixedMoment B raw6679step0 raw6679step0Labels := by
      have hz : ∀ j, raw6679 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6679step0 = (fun i j => raw6679 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6679step0 raw6679; decide +kernel
      have hl : raw6679step0Labels = raw6679Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6679 raw6679Labels permutation346 hz
    mixedMoment B raw6679step0 raw6679step0Labels = mixedMoment B raw6679step1 raw6679step1Labels := by
      have ha : raw6679step1 = (fun i j => raw6679step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6679step1 raw6679step0; decide +kernel
      have hl : raw6679step1Labels = raw6679step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6679step0 raw6679step0Labels permutation38 permutation2
    _ = mixedMoment B node1361 node1361Labels := by rfl

def raw6680 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw6680Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6680step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw6680step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6680 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6680 raw6680Labels = mixedMoment B node2976 node2976Labels := by
  calc
    mixedMoment B raw6680 raw6680Labels = mixedMoment B raw6680step0 raw6680step0Labels := by
      have ha : raw6680step0 = (fun i j => raw6680 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6680step0 raw6680; decide +kernel
      have hl : raw6680step0Labels = raw6680Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6680 raw6680Labels permutation182 permutation2
    _ = mixedMoment B node2976 node2976Labels := by rfl

def raw6681 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, 0, 0], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1]]
def raw6681Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6681step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1]]
def raw6681step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6681step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw6681step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6681 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6681 raw6681Labels = mixedMoment B node2884 node2884Labels := by
  calc
    mixedMoment B raw6681 raw6681Labels = mixedMoment B raw6681step0 raw6681step0Labels := by
      have hz : ∀ j, raw6681 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6681step0 = (fun i j => raw6681 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6681step0 raw6681; decide +kernel
      have hl : raw6681step0Labels = raw6681Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6681 raw6681Labels permutation346 hz
    mixedMoment B raw6681step0 raw6681step0Labels = mixedMoment B raw6681step1 raw6681step1Labels := by
      have ha : raw6681step1 = (fun i j => raw6681step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6681step1 raw6681step0; decide +kernel
      have hl : raw6681step1Labels = raw6681step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6681step0 raw6681step0Labels permutation38 permutation2
    _ = mixedMoment B node2884 node2884Labels := by rfl

def raw6682 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, 0, 0], ![0, -2, 2], ![0, 1, -1], ![2, -1, -1]]
def raw6682Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6682step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, -2, 2], ![0, 1, -1], ![2, -1, -1]]
def raw6682step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6682step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw6682step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6682 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6682 raw6682Labels = mixedMoment B node3039 node3039Labels := by
  calc
    mixedMoment B raw6682 raw6682Labels = mixedMoment B raw6682step0 raw6682step0Labels := by
      have hz : ∀ j, raw6682 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6682step0 = (fun i j => raw6682 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6682step0 raw6682; decide +kernel
      have hl : raw6682step0Labels = raw6682Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6682 raw6682Labels permutation346 hz
    mixedMoment B raw6682step0 raw6682step0Labels = mixedMoment B raw6682step1 raw6682step1Labels := by
      have ha : raw6682step1 = (fun i j => raw6682step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6682step1 raw6682step0; decide +kernel
      have hl : raw6682step1Labels = raw6682step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6682step0 raw6682step0Labels permutation40 permutation2
    _ = mixedMoment B node3039 node3039Labels := by rfl

def raw6683 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1]]
def raw6683Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6683step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1]]
def raw6683step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6683step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw6683step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6683 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6683 raw6683Labels = mixedMoment B node3053 node3053Labels := by
  calc
    mixedMoment B raw6683 raw6683Labels = mixedMoment B raw6683step0 raw6683step0Labels := by
      have hz : ∀ j, raw6683 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6683step0 = (fun i j => raw6683 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6683step0 raw6683; decide +kernel
      have hl : raw6683step0Labels = raw6683Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6683 raw6683Labels permutation346 hz
    mixedMoment B raw6683step0 raw6683step0Labels = mixedMoment B raw6683step1 raw6683step1Labels := by
      have ha : raw6683step1 = (fun i j => raw6683step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6683step1 raw6683step0; decide +kernel
      have hl : raw6683step1Labels = raw6683step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6683step0 raw6683step0Labels permutation38 permutation2
    _ = mixedMoment B node3053 node3053Labels := by rfl

def raw6684 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![1, -1, 0], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw6684Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6684step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw6684step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6684 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6684 raw6684Labels = mixedMoment B node3008 node3008Labels := by
  calc
    mixedMoment B raw6684 raw6684Labels = mixedMoment B raw6684step0 raw6684step0Labels := by
      have ha : raw6684step0 = (fun i j => raw6684 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6684step0 raw6684; decide +kernel
      have hl : raw6684step0Labels = raw6684Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6684 raw6684Labels permutation158 permutation2
    _ = mixedMoment B node3008 node3008Labels := by rfl

def raw6685 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, 0, 0], ![1, -3, 2], ![1, 0, -1], ![2, -1, -1]]
def raw6685Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6685step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![1, -3, 2], ![1, 0, -1], ![2, -1, -1]]
def raw6685step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6685step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![2, -3, 1], ![2, -1, -1]]
def raw6685step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6685 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6685 raw6685Labels = mixedMoment B node2627 node2627Labels := by
  calc
    mixedMoment B raw6685 raw6685Labels = mixedMoment B raw6685step0 raw6685step0Labels := by
      have hz : ∀ j, raw6685 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6685step0 = (fun i j => raw6685 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6685step0 raw6685; decide +kernel
      have hl : raw6685step0Labels = raw6685Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6685 raw6685Labels permutation346 hz
    mixedMoment B raw6685step0 raw6685step0Labels = mixedMoment B raw6685step1 raw6685step1Labels := by
      have ha : raw6685step1 = (fun i j => raw6685step0 (permutation102 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6685step1 raw6685step0; decide +kernel
      have hl : raw6685step1Labels = raw6685step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6685step0 raw6685step0Labels permutation102 permutation4
    _ = mixedMoment B node2627 node2627Labels := by rfl

def raw6686 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, 0, 0], ![0, -2, 2], ![2, -1, -1], ![2, -1, -1]]
def raw6686Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6686step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, -2, 2], ![2, -1, -1], ![2, -1, -1]]
def raw6686step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6686 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6686 raw6686Labels = mixedMoment B node3011 node3011Labels := by
  calc
    mixedMoment B raw6686 raw6686Labels = mixedMoment B raw6686step0 raw6686step0Labels := by
      have hz : ∀ j, raw6686 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6686step0 = (fun i j => raw6686 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6686step0 raw6686; decide +kernel
      have hl : raw6686step0Labels = raw6686Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6686 raw6686Labels permutation346 hz
    _ = mixedMoment B node3011 node3011Labels := by rfl

def raw6687 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![3, -2, -1]]
def raw6687Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6687step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![3, -2, -1]]
def raw6687step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6687step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![1, 0, -1], ![0, -2, 2], ![-1, 2, -1], ![-3, 2, 1]]
def raw6687step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6687step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![3, -2, -1]]
def raw6687step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6687 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6687 raw6687Labels = mixedMoment B node2946 node2946Labels := by
  calc
    mixedMoment B raw6687 raw6687Labels = mixedMoment B raw6687step0 raw6687step0Labels := by
      have hz : ∀ j, raw6687 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6687step0 = (fun i j => raw6687 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6687step0 raw6687; decide +kernel
      have hl : raw6687step0Labels = raw6687Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6687 raw6687Labels permutation346 hz
    mixedMoment B raw6687step0 raw6687step0Labels = mixedMoment B raw6687step1 raw6687step1Labels := by
      have ha : raw6687step1 = (fun i j => raw6687step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6687step1 raw6687step0; decide +kernel
      have hl : raw6687step1Labels = raw6687step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6687step0 raw6687step0Labels permutation151 permutation2
    mixedMoment B raw6687step1 raw6687step1Labels = mixedMoment B raw6687step2 raw6687step2Labels := by
      have ha : raw6687step2 = -raw6687step1 := by apply Matrix.ext; change ∀ i j, raw6687step2 i j = -(raw6687step1 i j); unfold raw6687step2 raw6687step1; decide +kernel
      have hl : raw6687step2Labels = raw6687step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2946 node2946Labels := by rfl

def raw6688 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1]]
def raw6688Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6688step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw6688step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6688 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6688 raw6688Labels = mixedMoment B node2862 node2862Labels := by
  calc
    mixedMoment B raw6688 raw6688Labels = mixedMoment B raw6688step0 raw6688step0Labels := by
      have ha : raw6688step0 = (fun i j => raw6688 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6688step0 raw6688; decide +kernel
      have hl : raw6688step0Labels = raw6688Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6688 raw6688Labels permutation200 permutation2
    _ = mixedMoment B node2862 node2862Labels := by rfl

def raw6689 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![0, -2, 2], ![0, 1, -1], ![2, -1, -1]]
def raw6689Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6689step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw6689step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6689 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6689 raw6689Labels = mixedMoment B node3029 node3029Labels := by
  calc
    mixedMoment B raw6689 raw6689Labels = mixedMoment B raw6689step0 raw6689step0Labels := by
      have ha : raw6689step0 = (fun i j => raw6689 (permutation202 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6689step0 raw6689; decide +kernel
      have hl : raw6689step0Labels = raw6689Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6689 raw6689Labels permutation202 permutation2
    _ = mixedMoment B node3029 node3029Labels := by rfl

def raw6690 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1]]
def raw6690Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6690step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw6690step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6690 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6690 raw6690Labels = mixedMoment B node3037 node3037Labels := by
  calc
    mixedMoment B raw6690 raw6690Labels = mixedMoment B raw6690step0 raw6690step0Labels := by
      have ha : raw6690step0 = (fun i j => raw6690 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6690step0 raw6690; decide +kernel
      have hl : raw6690step0Labels = raw6690Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6690 raw6690Labels permutation200 permutation2
    _ = mixedMoment B node3037 node3037Labels := by rfl

def raw6691 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, 1, 0], ![1, -3, 2], ![1, 0, -1], ![2, -1, -1]]
def raw6691Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6691step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -3, 1]]
def raw6691step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6691 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6691 raw6691Labels = mixedMoment B node2625 node2625Labels := by
  calc
    mixedMoment B raw6691 raw6691Labels = mixedMoment B raw6691step0 raw6691step0Labels := by
      have ha : raw6691step0 = (fun i j => raw6691 (permutation519 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6691step0 raw6691; decide +kernel
      have hl : raw6691step0Labels = raw6691Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6691 raw6691Labels permutation519 permutation4
    _ = mixedMoment B node2625 node2625Labels := by rfl

def raw6692 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, 1, 0], ![0, -2, 2], ![2, -1, -1], ![2, -1, -1]]
def raw6692Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6692step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw6692step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6692 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6692 raw6692Labels = mixedMoment B node2972 node2972Labels := by
  calc
    mixedMoment B raw6692 raw6692Labels = mixedMoment B raw6692step0 raw6692step0Labels := by
      have ha : raw6692step0 = (fun i j => raw6692 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6692step0 raw6692; decide +kernel
      have hl : raw6692step0Labels = raw6692Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6692 raw6692Labels permutation182 permutation2
    _ = mixedMoment B node2972 node2972Labels := by rfl

def raw6693 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![3, -2, -1]]
def raw6693Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6693step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![1, 0, -1], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-3, 2, 1]]
def raw6693step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6693step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw6693step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6693 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6693 raw6693Labels = mixedMoment B node2918 node2918Labels := by
  calc
    mixedMoment B raw6693 raw6693Labels = mixedMoment B raw6693step0 raw6693step0Labels := by
      have ha : raw6693step0 = (fun i j => raw6693 (permutation676 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6693step0 raw6693; decide +kernel
      have hl : raw6693step0Labels = raw6693Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6693 raw6693Labels permutation676 permutation2
    mixedMoment B raw6693step0 raw6693step0Labels = mixedMoment B raw6693step1 raw6693step1Labels := by
      have ha : raw6693step1 = -raw6693step0 := by apply Matrix.ext; change ∀ i j, raw6693step1 i j = -(raw6693step0 i j); unfold raw6693step1 raw6693step0; decide +kernel
      have hl : raw6693step1Labels = raw6693step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2918 node2918Labels := by rfl

def raw6694 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![0, 1, -1], ![2, -1, -1]]
def raw6694Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6694step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -3, 2], ![0, 1, -1], ![2, -1, -1]]
def raw6694step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6694step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw6694step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6694 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6694 raw6694Labels = mixedMoment B node2641 node2641Labels := by
  calc
    mixedMoment B raw6694 raw6694Labels = mixedMoment B raw6694step0 raw6694step0Labels := by
      have hz : ∀ j, raw6694 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6694step0 = (fun i j => raw6694 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6694step0 raw6694; decide +kernel
      have hl : raw6694step0Labels = raw6694Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6694 raw6694Labels permutation346 hz
    mixedMoment B raw6694step0 raw6694step0Labels = mixedMoment B raw6694step1 raw6694step1Labels := by
      have ha : raw6694step1 = (fun i j => raw6694step0 (permutation101 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6694step1 raw6694step0; decide +kernel
      have hl : raw6694step1Labels = raw6694step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6694step0 raw6694step0Labels permutation101 permutation4
    _ = mixedMoment B node2641 node2641Labels := by rfl

def raw6695 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1]]
def raw6695Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6695step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1]]
def raw6695step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6695step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw6695step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6695 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6695 raw6695Labels = mixedMoment B node2754 node2754Labels := by
  calc
    mixedMoment B raw6695 raw6695Labels = mixedMoment B raw6695step0 raw6695step0Labels := by
      have hz : ∀ j, raw6695 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6695step0 = (fun i j => raw6695 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6695step0 raw6695; decide +kernel
      have hl : raw6695step0Labels = raw6695Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6695 raw6695Labels permutation346 hz
    mixedMoment B raw6695step0 raw6695step0Labels = mixedMoment B raw6695step1 raw6695step1Labels := by
      have ha : raw6695step1 = (fun i j => raw6695step0 (permutation97 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6695step1 raw6695step0; decide +kernel
      have hl : raw6695step1Labels = raw6695step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6695step0 raw6695step0Labels permutation97 permutation4
    _ = mixedMoment B node2754 node2754Labels := by rfl

def raw6696 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![-1, -1, 2], ![2, -1, -1], ![2, -1, -1]]
def raw6696Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6696step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, -1, 2], ![2, -1, -1], ![2, -1, -1]]
def raw6696step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6696step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw6696step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6696 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6696 raw6696Labels = mixedMoment B node2868 node2868Labels := by
  calc
    mixedMoment B raw6696 raw6696Labels = mixedMoment B raw6696step0 raw6696step0Labels := by
      have hz : ∀ j, raw6696 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6696step0 = (fun i j => raw6696 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6696step0 raw6696; decide +kernel
      have hl : raw6696step0Labels = raw6696Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6696 raw6696Labels permutation346 hz
    mixedMoment B raw6696step0 raw6696step0Labels = mixedMoment B raw6696step1 raw6696step1Labels := by
      have ha : raw6696step1 = (fun i j => raw6696step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6696step1 raw6696step0; decide +kernel
      have hl : raw6696step1Labels = raw6696step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6696step0 raw6696step0Labels permutation38 permutation2
    _ = mixedMoment B node2868 node2868Labels := by rfl

def raw6697 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![-1, -1, 2], ![1, 0, -1], ![3, -2, -1]]
def raw6697Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6697step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, -1, 2], ![1, 0, -1], ![3, -2, -1]]
def raw6697step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6697step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw6697step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6697 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6697 raw6697Labels = mixedMoment B node2865 node2865Labels := by
  calc
    mixedMoment B raw6697 raw6697Labels = mixedMoment B raw6697step0 raw6697step0Labels := by
      have hz : ∀ j, raw6697 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6697step0 = (fun i j => raw6697 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6697step0 raw6697; decide +kernel
      have hl : raw6697step0Labels = raw6697Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6697 raw6697Labels permutation346 hz
    mixedMoment B raw6697step0 raw6697step0Labels = mixedMoment B raw6697step1 raw6697step1Labels := by
      have ha : raw6697step1 = (fun i j => raw6697step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6697step1 raw6697step0; decide +kernel
      have hl : raw6697step1Labels = raw6697step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6697step0 raw6697step0Labels permutation38 permutation2
    _ = mixedMoment B node2865 node2865Labels := by rfl

def raw6698 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![2, -1, -1], ![1, 0, -1]]
def raw6698Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6698step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -2, 2], ![2, -1, -1], ![1, 0, -1]]
def raw6698step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6698step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw6698step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6698 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6698 raw6698Labels = mixedMoment B node3039 node3039Labels := by
  calc
    mixedMoment B raw6698 raw6698Labels = mixedMoment B raw6698step0 raw6698step0Labels := by
      have hz : ∀ j, raw6698 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6698step0 = (fun i j => raw6698 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6698step0 raw6698; decide +kernel
      have hl : raw6698step0Labels = raw6698Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6698 raw6698Labels permutation346 hz
    mixedMoment B raw6698step0 raw6698step0Labels = mixedMoment B raw6698step1 raw6698step1Labels := by
      have ha : raw6698step1 = (fun i j => raw6698step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6698step1 raw6698step0; decide +kernel
      have hl : raw6698step1Labels = raw6698step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6698step0 raw6698step0Labels permutation39 permutation2
    _ = mixedMoment B node3039 node3039Labels := by rfl

def raw6699 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![0, 1, -1], ![3, -2, -1]]
def raw6699Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6699step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -2, 2], ![0, 1, -1], ![3, -2, -1]]
def raw6699step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6699step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw6699step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6699 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6699 raw6699Labels = mixedMoment B node3031 node3031Labels := by
  calc
    mixedMoment B raw6699 raw6699Labels = mixedMoment B raw6699step0 raw6699step0Labels := by
      have hz : ∀ j, raw6699 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6699step0 = (fun i j => raw6699 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6699step0 raw6699; decide +kernel
      have hl : raw6699step0Labels = raw6699Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6699 raw6699Labels permutation346 hz
    mixedMoment B raw6699step0 raw6699step0Labels = mixedMoment B raw6699step1 raw6699step1Labels := by
      have ha : raw6699step1 = (fun i j => raw6699step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6699step1 raw6699step0; decide +kernel
      have hl : raw6699step1Labels = raw6699step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6699step0 raw6699step0Labels permutation38 permutation2
    _ = mixedMoment B node3031 node3031Labels := by rfl

def raw6700 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-2, 2, 0], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6700Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6700step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-2, 2, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6700step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6700step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw6700step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw6700step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw6700step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6700 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6700 raw6700Labels = mixedMoment B node5233 node5233Labels := by
  calc
    mixedMoment B raw6700 raw6700Labels = mixedMoment B raw6700step0 raw6700step0Labels := by
      have hz : ∀ j, raw6700 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6700step0 = (fun i j => raw6700 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6700step0 raw6700; decide +kernel
      have hl : raw6700step0Labels = raw6700Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6700 raw6700Labels permutation346 hz
    mixedMoment B raw6700step0 raw6700step0Labels = mixedMoment B raw6700step1 raw6700step1Labels := by
      have ha : raw6700step1 = (fun i j => raw6700step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw6700step1 raw6700step0; decide +kernel
      have hl : raw6700step1Labels = raw6700step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6700step0 raw6700step0Labels permutation38 permutation7
    mixedMoment B raw6700step1 raw6700step1Labels = mixedMoment B raw6700step2 raw6700step2Labels := by
      have ha : raw6700step2 = raw6700step1 := by apply Matrix.ext; unfold raw6700step2 raw6700step1; decide +kernel
      have hl : raw6700step1Labels = labelEmbedding10 ∘ raw6700step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6700step1 raw6700step1Labels raw6700step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5233 node5233Labels := by rfl

def raw6701 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6701Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6701step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw6701step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw6701step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw6701step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6701 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6701 raw6701Labels = mixedMoment B node5220 node5220Labels := by
  calc
    mixedMoment B raw6701 raw6701Labels = mixedMoment B raw6701step0 raw6701step0Labels := by
      have ha : raw6701step0 = (fun i j => raw6701 (permutation200 i) (permutation7 j)) := by apply Matrix.ext; unfold raw6701step0 raw6701; decide +kernel
      have hl : raw6701step0Labels = raw6701Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6701 raw6701Labels permutation200 permutation7
    mixedMoment B raw6701step0 raw6701step0Labels = mixedMoment B raw6701step1 raw6701step1Labels := by
      have ha : raw6701step1 = raw6701step0 := by apply Matrix.ext; unfold raw6701step1 raw6701step0; decide +kernel
      have hl : raw6701step0Labels = labelEmbedding10 ∘ raw6701step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6701step0 raw6701step0Labels raw6701step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5220 node5220Labels := by rfl

def raw6702 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6702Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6702step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6702step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6702step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw6702step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw6702step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw6702step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6702 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6702 raw6702Labels = mixedMoment B node5259 node5259Labels := by
  calc
    mixedMoment B raw6702 raw6702Labels = mixedMoment B raw6702step0 raw6702step0Labels := by
      have hz : ∀ j, raw6702 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6702step0 = (fun i j => raw6702 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6702step0 raw6702; decide +kernel
      have hl : raw6702step0Labels = raw6702Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6702 raw6702Labels permutation346 hz
    mixedMoment B raw6702step0 raw6702step0Labels = mixedMoment B raw6702step1 raw6702step1Labels := by
      have ha : raw6702step1 = (fun i j => raw6702step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw6702step1 raw6702step0; decide +kernel
      have hl : raw6702step1Labels = raw6702step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6702step0 raw6702step0Labels permutation38 permutation7
    mixedMoment B raw6702step1 raw6702step1Labels = mixedMoment B raw6702step2 raw6702step2Labels := by
      have ha : raw6702step2 = raw6702step1 := by apply Matrix.ext; unfold raw6702step2 raw6702step1; decide +kernel
      have hl : raw6702step1Labels = labelEmbedding10 ∘ raw6702step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6702step1 raw6702step1Labels raw6702step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5259 node5259Labels := by rfl

def raw6703 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw6703Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6703step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw6703step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6703step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw6703step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw6703step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw6703step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6703 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6703 raw6703Labels = mixedMoment B node5229 node5229Labels := by
  calc
    mixedMoment B raw6703 raw6703Labels = mixedMoment B raw6703step0 raw6703step0Labels := by
      have hz : ∀ j, raw6703 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6703step0 = (fun i j => raw6703 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6703step0 raw6703; decide +kernel
      have hl : raw6703step0Labels = raw6703Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6703 raw6703Labels permutation346 hz
    mixedMoment B raw6703step0 raw6703step0Labels = mixedMoment B raw6703step1 raw6703step1Labels := by
      have ha : raw6703step1 = (fun i j => raw6703step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw6703step1 raw6703step0; decide +kernel
      have hl : raw6703step1Labels = raw6703step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6703step0 raw6703step0Labels permutation38 permutation7
    mixedMoment B raw6703step1 raw6703step1Labels = mixedMoment B raw6703step2 raw6703step2Labels := by
      have ha : raw6703step2 = raw6703step1 := by apply Matrix.ext; unfold raw6703step2 raw6703step1; decide +kernel
      have hl : raw6703step1Labels = labelEmbedding10 ∘ raw6703step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6703step1 raw6703step1Labels raw6703step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5229 node5229Labels := by rfl

def raw6704 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw6704Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6704step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw6704step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6704step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw6704step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw6704step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw6704step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6704 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6704 raw6704Labels = mixedMoment B node5228 node5228Labels := by
  calc
    mixedMoment B raw6704 raw6704Labels = mixedMoment B raw6704step0 raw6704step0Labels := by
      have hz : ∀ j, raw6704 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6704step0 = (fun i j => raw6704 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6704step0 raw6704; decide +kernel
      have hl : raw6704step0Labels = raw6704Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6704 raw6704Labels permutation346 hz
    mixedMoment B raw6704step0 raw6704step0Labels = mixedMoment B raw6704step1 raw6704step1Labels := by
      have ha : raw6704step1 = (fun i j => raw6704step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw6704step1 raw6704step0; decide +kernel
      have hl : raw6704step1Labels = raw6704step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6704step0 raw6704step0Labels permutation38 permutation7
    mixedMoment B raw6704step1 raw6704step1Labels = mixedMoment B raw6704step2 raw6704step2Labels := by
      have ha : raw6704step2 = raw6704step1 := by apply Matrix.ext; unfold raw6704step2 raw6704step1; decide +kernel
      have hl : raw6704step1Labels = labelEmbedding10 ∘ raw6704step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6704step1 raw6704step1Labels raw6704step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5228 node5228Labels := by rfl

def raw6705 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6705Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6705step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6705step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6705step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6705step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6705step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw6705step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw6705step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6705step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw6705step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6705step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6705 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6705 raw6705Labels = mixedMoment B node4896 node4896Labels := by
  calc
    mixedMoment B raw6705 raw6705Labels = mixedMoment B raw6705step0 raw6705step0Labels := by
      have hz : ∀ j, raw6705 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6705step0 = (fun i j => raw6705 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6705step0 raw6705; decide +kernel
      have hl : raw6705step0Labels = raw6705Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6705 raw6705Labels permutation346 hz
    mixedMoment B raw6705step0 raw6705step0Labels = mixedMoment B raw6705step1 raw6705step1Labels := by
      have hz : ∀ j, raw6705step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw6705step1 = (fun i j => raw6705step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw6705step1 raw6705step0; decide +kernel
      have hl : raw6705step1Labels = raw6705step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6705step0 raw6705step0Labels permutation56 hz
    mixedMoment B raw6705step1 raw6705step1Labels = mixedMoment B raw6705step2 raw6705step2Labels := by
      have ha : raw6705step2 = (fun i j => raw6705step1 (permutation11 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6705step2 raw6705step1; decide +kernel
      have hl : raw6705step2Labels = raw6705step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6705step1 raw6705step1Labels permutation11 permutation4
    mixedMoment B raw6705step2 raw6705step2Labels = mixedMoment B raw6705step3 raw6705step3Labels := by
      have ha : raw6705step3 = -raw6705step2 := by apply Matrix.ext; change ∀ i j, raw6705step3 i j = -(raw6705step2 i j); unfold raw6705step3 raw6705step2; decide +kernel
      have hl : raw6705step3Labels = raw6705step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6705step3 raw6705step3Labels = mixedMoment B raw6705step4 raw6705step4Labels := by
      have ha : raw6705step4 = raw6705step3 := by apply Matrix.ext; unfold raw6705step4 raw6705step3; decide +kernel
      have hl : raw6705step3Labels = labelEmbedding7 ∘ raw6705step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6705step3 raw6705step3Labels raw6705step4Labels labelEmbedding7 hl
    _ = mixedMoment B node4896 node4896Labels := by rfl

def raw6706 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6706Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6706step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6706step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6706step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6706step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw6706step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6706step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6706 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6706 raw6706Labels = mixedMoment B node5266 node5266Labels := by
  calc
    mixedMoment B raw6706 raw6706Labels = mixedMoment B raw6706step0 raw6706step0Labels := by
      have hz : ∀ j, raw6706 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw6706step0 = (fun i j => raw6706 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw6706step0 raw6706; decide +kernel
      have hl : raw6706step0Labels = raw6706Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6706 raw6706Labels permutation265 hz
    mixedMoment B raw6706step0 raw6706step0Labels = mixedMoment B raw6706step1 raw6706step1Labels := by
      have ha : raw6706step1 = (fun i j => raw6706step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6706step1 raw6706step0; decide +kernel
      have hl : raw6706step1Labels = raw6706step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6706step0 raw6706step0Labels permutation32 permutation6
    mixedMoment B raw6706step1 raw6706step1Labels = mixedMoment B raw6706step2 raw6706step2Labels := by
      have ha : raw6706step2 = raw6706step1 := by apply Matrix.ext; unfold raw6706step2 raw6706step1; decide +kernel
      have hl : raw6706step1Labels = labelEmbedding9 ∘ raw6706step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6706step1 raw6706step1Labels raw6706step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5266 node5266Labels := by rfl

def raw6707 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6707Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6707step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6707step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6707step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6707step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6707step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw6707step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw6707step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw6707step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6707 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6707 raw6707Labels = mixedMoment B node5293 node5293Labels := by
  calc
    mixedMoment B raw6707 raw6707Labels = mixedMoment B raw6707step0 raw6707step0Labels := by
      have hz : ∀ j, raw6707 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6707step0 = (fun i j => raw6707 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6707step0 raw6707; decide +kernel
      have hl : raw6707step0Labels = raw6707Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6707 raw6707Labels permutation346 hz
    mixedMoment B raw6707step0 raw6707step0Labels = mixedMoment B raw6707step1 raw6707step1Labels := by
      have hz : ∀ j, raw6707step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw6707step1 = (fun i j => raw6707step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw6707step1 raw6707step0; decide +kernel
      have hl : raw6707step1Labels = raw6707step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6707step0 raw6707step0Labels permutation56 hz
    mixedMoment B raw6707step1 raw6707step1Labels = mixedMoment B raw6707step2 raw6707step2Labels := by
      have ha : raw6707step2 = (fun i j => raw6707step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6707step2 raw6707step1; decide +kernel
      have hl : raw6707step2Labels = raw6707step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6707step1 raw6707step1Labels permutation8 permutation6
    mixedMoment B raw6707step2 raw6707step2Labels = mixedMoment B raw6707step3 raw6707step3Labels := by
      have ha : raw6707step3 = raw6707step2 := by apply Matrix.ext; unfold raw6707step3 raw6707step2; decide +kernel
      have hl : raw6707step2Labels = labelEmbedding9 ∘ raw6707step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6707step2 raw6707step2Labels raw6707step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5293 node5293Labels := by rfl

def raw6708 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw6708Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6708step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw6708step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6708step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw6708step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6708step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw6708step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw6708step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw6708step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6708 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6708 raw6708Labels = mixedMoment B node5300 node5300Labels := by
  calc
    mixedMoment B raw6708 raw6708Labels = mixedMoment B raw6708step0 raw6708step0Labels := by
      have hz : ∀ j, raw6708 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6708step0 = (fun i j => raw6708 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6708step0 raw6708; decide +kernel
      have hl : raw6708step0Labels = raw6708Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6708 raw6708Labels permutation346 hz
    mixedMoment B raw6708step0 raw6708step0Labels = mixedMoment B raw6708step1 raw6708step1Labels := by
      have hz : ∀ j, raw6708step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw6708step1 = (fun i j => raw6708step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw6708step1 raw6708step0; decide +kernel
      have hl : raw6708step1Labels = raw6708step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6708step0 raw6708step0Labels permutation56 hz
    mixedMoment B raw6708step1 raw6708step1Labels = mixedMoment B raw6708step2 raw6708step2Labels := by
      have ha : raw6708step2 = (fun i j => raw6708step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6708step2 raw6708step1; decide +kernel
      have hl : raw6708step2Labels = raw6708step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6708step1 raw6708step1Labels permutation8 permutation6
    mixedMoment B raw6708step2 raw6708step2Labels = mixedMoment B raw6708step3 raw6708step3Labels := by
      have ha : raw6708step3 = raw6708step2 := by apply Matrix.ext; unfold raw6708step3 raw6708step2; decide +kernel
      have hl : raw6708step2Labels = labelEmbedding9 ∘ raw6708step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6708step2 raw6708step2Labels raw6708step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5300 node5300Labels := by rfl

def raw6709 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw6709Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6709step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw6709step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6709step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw6709step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6709step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw6709step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw6709step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw6709step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6709 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6709 raw6709Labels = mixedMoment B node5302 node5302Labels := by
  calc
    mixedMoment B raw6709 raw6709Labels = mixedMoment B raw6709step0 raw6709step0Labels := by
      have hz : ∀ j, raw6709 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6709step0 = (fun i j => raw6709 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6709step0 raw6709; decide +kernel
      have hl : raw6709step0Labels = raw6709Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6709 raw6709Labels permutation346 hz
    mixedMoment B raw6709step0 raw6709step0Labels = mixedMoment B raw6709step1 raw6709step1Labels := by
      have hz : ∀ j, raw6709step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw6709step1 = (fun i j => raw6709step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw6709step1 raw6709step0; decide +kernel
      have hl : raw6709step1Labels = raw6709step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6709step0 raw6709step0Labels permutation56 hz
    mixedMoment B raw6709step1 raw6709step1Labels = mixedMoment B raw6709step2 raw6709step2Labels := by
      have ha : raw6709step2 = (fun i j => raw6709step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6709step2 raw6709step1; decide +kernel
      have hl : raw6709step2Labels = raw6709step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6709step1 raw6709step1Labels permutation8 permutation6
    mixedMoment B raw6709step2 raw6709step2Labels = mixedMoment B raw6709step3 raw6709step3Labels := by
      have ha : raw6709step3 = raw6709step2 := by apply Matrix.ext; unfold raw6709step3 raw6709step2; decide +kernel
      have hl : raw6709step2Labels = labelEmbedding9 ∘ raw6709step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6709step2 raw6709step2Labels raw6709step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5302 node5302Labels := by rfl

def raw6710 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6710Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6710step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw6710step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw6710step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw6710step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw6710step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw6710step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6710 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6710 raw6710Labels = mixedMoment B node4803 node4803Labels := by
  calc
    mixedMoment B raw6710 raw6710Labels = mixedMoment B raw6710step0 raw6710step0Labels := by
      have ha : raw6710step0 = (fun i j => raw6710 (permutation165 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6710step0 raw6710; decide +kernel
      have hl : raw6710step0Labels = raw6710Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6710 raw6710Labels permutation165 permutation4
    mixedMoment B raw6710step0 raw6710step0Labels = mixedMoment B raw6710step1 raw6710step1Labels := by
      have ha : raw6710step1 = -raw6710step0 := by apply Matrix.ext; change ∀ i j, raw6710step1 i j = -(raw6710step0 i j); unfold raw6710step1 raw6710step0; decide +kernel
      have hl : raw6710step1Labels = raw6710step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6710step1 raw6710step1Labels = mixedMoment B raw6710step2 raw6710step2Labels := by
      have ha : raw6710step2 = raw6710step1 := by apply Matrix.ext; unfold raw6710step2 raw6710step1; decide +kernel
      have hl : raw6710step1Labels = labelEmbedding7 ∘ raw6710step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6710step1 raw6710step1Labels raw6710step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4803 node4803Labels := by rfl

def raw6711 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6711Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6711step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6711step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw6711step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6711step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6711 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6711 raw6711Labels = mixedMoment B node5223 node5223Labels := by
  calc
    mixedMoment B raw6711 raw6711Labels = mixedMoment B raw6711step0 raw6711step0Labels := by
      have ha : raw6711step0 = (fun i j => raw6711 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6711step0 raw6711; decide +kernel
      have hl : raw6711step0Labels = raw6711Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6711 raw6711Labels permutation152 permutation6
    mixedMoment B raw6711step0 raw6711step0Labels = mixedMoment B raw6711step1 raw6711step1Labels := by
      have ha : raw6711step1 = raw6711step0 := by apply Matrix.ext; unfold raw6711step1 raw6711step0; decide +kernel
      have hl : raw6711step0Labels = labelEmbedding9 ∘ raw6711step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6711step0 raw6711step0Labels raw6711step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5223 node5223Labels := by rfl

def raw6712 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6712Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6712step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw6712step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw6712step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw6712step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6712 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6712 raw6712Labels = mixedMoment B node5250 node5250Labels := by
  calc
    mixedMoment B raw6712 raw6712Labels = mixedMoment B raw6712step0 raw6712step0Labels := by
      have ha : raw6712step0 = (fun i j => raw6712 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6712step0 raw6712; decide +kernel
      have hl : raw6712step0Labels = raw6712Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6712 raw6712Labels permutation152 permutation6
    mixedMoment B raw6712step0 raw6712step0Labels = mixedMoment B raw6712step1 raw6712step1Labels := by
      have ha : raw6712step1 = raw6712step0 := by apply Matrix.ext; unfold raw6712step1 raw6712step0; decide +kernel
      have hl : raw6712step0Labels = labelEmbedding9 ∘ raw6712step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6712step0 raw6712step0Labels raw6712step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5250 node5250Labels := by rfl

def raw6713 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw6713Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6713step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw6713step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw6713step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw6713step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6713 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6713 raw6713Labels = mixedMoment B node5253 node5253Labels := by
  calc
    mixedMoment B raw6713 raw6713Labels = mixedMoment B raw6713step0 raw6713step0Labels := by
      have ha : raw6713step0 = (fun i j => raw6713 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6713step0 raw6713; decide +kernel
      have hl : raw6713step0Labels = raw6713Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6713 raw6713Labels permutation152 permutation6
    mixedMoment B raw6713step0 raw6713step0Labels = mixedMoment B raw6713step1 raw6713step1Labels := by
      have ha : raw6713step1 = raw6713step0 := by apply Matrix.ext; unfold raw6713step1 raw6713step0; decide +kernel
      have hl : raw6713step0Labels = labelEmbedding9 ∘ raw6713step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6713step0 raw6713step0Labels raw6713step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5253 node5253Labels := by rfl

def raw6714 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw6714Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6714step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw6714step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw6714step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw6714step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6714 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6714 raw6714Labels = mixedMoment B node5254 node5254Labels := by
  calc
    mixedMoment B raw6714 raw6714Labels = mixedMoment B raw6714step0 raw6714step0Labels := by
      have ha : raw6714step0 = (fun i j => raw6714 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6714step0 raw6714; decide +kernel
      have hl : raw6714step0Labels = raw6714Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6714 raw6714Labels permutation152 permutation6
    mixedMoment B raw6714step0 raw6714step0Labels = mixedMoment B raw6714step1 raw6714step1Labels := by
      have ha : raw6714step1 = raw6714step0 := by apply Matrix.ext; unfold raw6714step1 raw6714step0; decide +kernel
      have hl : raw6714step0Labels = labelEmbedding9 ∘ raw6714step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6714step0 raw6714step0Labels raw6714step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5254 node5254Labels := by rfl

def raw6715 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![0, 0, 0], ![3, -3, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6715Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6715step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![3, -3, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6715step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6715step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-3, 3, 0]]
def raw6715step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw6715step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw6715step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw6715step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw6715step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6715 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6715 raw6715Labels = mixedMoment B node4808 node4808Labels := by
  calc
    mixedMoment B raw6715 raw6715Labels = mixedMoment B raw6715step0 raw6715step0Labels := by
      have hz : ∀ j, raw6715 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6715step0 = (fun i j => raw6715 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6715step0 raw6715; decide +kernel
      have hl : raw6715step0Labels = raw6715Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6715 raw6715Labels permutation346 hz
    mixedMoment B raw6715step0 raw6715step0Labels = mixedMoment B raw6715step1 raw6715step1Labels := by
      have ha : raw6715step1 = (fun i j => raw6715step0 (permutation35 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6715step1 raw6715step0; decide +kernel
      have hl : raw6715step1Labels = raw6715step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6715step0 raw6715step0Labels permutation35 permutation4
    mixedMoment B raw6715step1 raw6715step1Labels = mixedMoment B raw6715step2 raw6715step2Labels := by
      have ha : raw6715step2 = -raw6715step1 := by apply Matrix.ext; change ∀ i j, raw6715step2 i j = -(raw6715step1 i j); unfold raw6715step2 raw6715step1; decide +kernel
      have hl : raw6715step2Labels = raw6715step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6715step2 raw6715step2Labels = mixedMoment B raw6715step3 raw6715step3Labels := by
      have ha : raw6715step3 = raw6715step2 := by apply Matrix.ext; unfold raw6715step3 raw6715step2; decide +kernel
      have hl : raw6715step2Labels = labelEmbedding7 ∘ raw6715step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6715step2 raw6715step2Labels raw6715step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4808 node4808Labels := by rfl

def raw6716 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![0, 0, 0], ![3, -3, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6716Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6716step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![3, -3, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6716step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6716step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw6716step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw6716step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw6716step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6716 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6716 raw6716Labels = mixedMoment B node4855 node4855Labels := by
  calc
    mixedMoment B raw6716 raw6716Labels = mixedMoment B raw6716step0 raw6716step0Labels := by
      have hz : ∀ j, raw6716 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6716step0 = (fun i j => raw6716 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6716step0 raw6716; decide +kernel
      have hl : raw6716step0Labels = raw6716Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6716 raw6716Labels permutation346 hz
    mixedMoment B raw6716step0 raw6716step0Labels = mixedMoment B raw6716step1 raw6716step1Labels := by
      have ha : raw6716step1 = (fun i j => raw6716step0 (permutation102 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6716step1 raw6716step0; decide +kernel
      have hl : raw6716step1Labels = raw6716step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6716step0 raw6716step0Labels permutation102 permutation5
    mixedMoment B raw6716step1 raw6716step1Labels = mixedMoment B raw6716step2 raw6716step2Labels := by
      have ha : raw6716step2 = raw6716step1 := by apply Matrix.ext; unfold raw6716step2 raw6716step1; decide +kernel
      have hl : raw6716step1Labels = labelEmbedding8 ∘ raw6716step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6716step1 raw6716step1Labels raw6716step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4855 node4855Labels := by rfl

def raw6717 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 1, 0], ![3, -3, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6717Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6717step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw6717step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw6717step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw6717step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6717 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6717 raw6717Labels = mixedMoment B node4854 node4854Labels := by
  calc
    mixedMoment B raw6717 raw6717Labels = mixedMoment B raw6717step0 raw6717step0Labels := by
      have ha : raw6717step0 = (fun i j => raw6717 (permutation517 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6717step0 raw6717; decide +kernel
      have hl : raw6717step0Labels = raw6717Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6717 raw6717Labels permutation517 permutation5
    mixedMoment B raw6717step0 raw6717step0Labels = mixedMoment B raw6717step1 raw6717step1Labels := by
      have ha : raw6717step1 = raw6717step0 := by apply Matrix.ext; unfold raw6717step1 raw6717step0; decide +kernel
      have hl : raw6717step0Labels = labelEmbedding8 ∘ raw6717step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6717step0 raw6717step0Labels raw6717step1Labels labelEmbedding8 hl
    _ = mixedMoment B node4854 node4854Labels := by rfl

def raw6718 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![3, -3, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw6718Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6718step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![3, -3, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw6718step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6718step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw6718step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw6718step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw6718step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6718 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6718 raw6718Labels = mixedMoment B node4870 node4870Labels := by
  calc
    mixedMoment B raw6718 raw6718Labels = mixedMoment B raw6718step0 raw6718step0Labels := by
      have hz : ∀ j, raw6718 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6718step0 = (fun i j => raw6718 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6718step0 raw6718; decide +kernel
      have hl : raw6718step0Labels = raw6718Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6718 raw6718Labels permutation346 hz
    mixedMoment B raw6718step0 raw6718step0Labels = mixedMoment B raw6718step1 raw6718step1Labels := by
      have ha : raw6718step1 = (fun i j => raw6718step0 (permutation101 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6718step1 raw6718step0; decide +kernel
      have hl : raw6718step1Labels = raw6718step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6718step0 raw6718step0Labels permutation101 permutation5
    mixedMoment B raw6718step1 raw6718step1Labels = mixedMoment B raw6718step2 raw6718step2Labels := by
      have ha : raw6718step2 = raw6718step1 := by apply Matrix.ext; unfold raw6718step2 raw6718step1; decide +kernel
      have hl : raw6718step1Labels = labelEmbedding8 ∘ raw6718step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6718step1 raw6718step1Labels raw6718step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4870 node4870Labels := by rfl

def raw6719 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![3, -3, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw6719Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6719step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![3, -3, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw6719step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6719step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw6719step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw6719step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw6719step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw6719step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw6719step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6719 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6719 raw6719Labels = mixedMoment B node4880 node4880Labels := by
  calc
    mixedMoment B raw6719 raw6719Labels = mixedMoment B raw6719step0 raw6719step0Labels := by
      have hz : ∀ j, raw6719 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6719step0 = (fun i j => raw6719 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6719step0 raw6719; decide +kernel
      have hl : raw6719step0Labels = raw6719Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6719 raw6719Labels permutation346 hz
    mixedMoment B raw6719step0 raw6719step0Labels = mixedMoment B raw6719step1 raw6719step1Labels := by
      have ha : raw6719step1 = (fun i j => raw6719step0 (permutation82 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6719step1 raw6719step0; decide +kernel
      have hl : raw6719step1Labels = raw6719step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6719step0 raw6719step0Labels permutation82 permutation3
    mixedMoment B raw6719step1 raw6719step1Labels = mixedMoment B raw6719step2 raw6719step2Labels := by
      have ha : raw6719step2 = -raw6719step1 := by apply Matrix.ext; change ∀ i j, raw6719step2 i j = -(raw6719step1 i j); unfold raw6719step2 raw6719step1; decide +kernel
      have hl : raw6719step2Labels = raw6719step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6719step2 raw6719step2Labels = mixedMoment B raw6719step3 raw6719step3Labels := by
      have ha : raw6719step3 = raw6719step2 := by apply Matrix.ext; unfold raw6719step3 raw6719step2; decide +kernel
      have hl : raw6719step2Labels = labelEmbedding6 ∘ raw6719step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6719step2 raw6719step2Labels raw6719step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4880 node4880Labels := by rfl

def raw6720 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw6720Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6720step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![2, -2, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw6720step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6720step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw6720step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw6720step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6720step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw6720step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6720step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6720 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6720 raw6720Labels = mixedMoment B node4839 node4839Labels := by
  calc
    mixedMoment B raw6720 raw6720Labels = mixedMoment B raw6720step0 raw6720step0Labels := by
      have hz : ∀ j, raw6720 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6720step0 = (fun i j => raw6720 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6720step0 raw6720; decide +kernel
      have hl : raw6720step0Labels = raw6720Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6720 raw6720Labels permutation346 hz
    mixedMoment B raw6720step0 raw6720step0Labels = mixedMoment B raw6720step1 raw6720step1Labels := by
      have ha : raw6720step1 = (fun i j => raw6720step0 (permutation35 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6720step1 raw6720step0; decide +kernel
      have hl : raw6720step1Labels = raw6720step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6720step0 raw6720step0Labels permutation35 permutation4
    mixedMoment B raw6720step1 raw6720step1Labels = mixedMoment B raw6720step2 raw6720step2Labels := by
      have ha : raw6720step2 = -raw6720step1 := by apply Matrix.ext; change ∀ i j, raw6720step2 i j = -(raw6720step1 i j); unfold raw6720step2 raw6720step1; decide +kernel
      have hl : raw6720step2Labels = raw6720step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6720step2 raw6720step2Labels = mixedMoment B raw6720step3 raw6720step3Labels := by
      have ha : raw6720step3 = raw6720step2 := by apply Matrix.ext; unfold raw6720step3 raw6720step2; decide +kernel
      have hl : raw6720step2Labels = labelEmbedding7 ∘ raw6720step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6720step2 raw6720step2Labels raw6720step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4839 node4839Labels := by rfl

def raw6721 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![0, 0, 0], ![2, -2, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw6721Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6721step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![2, -2, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw6721step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6721step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw6721step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw6721step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw6721step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6721 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6721 raw6721Labels = mixedMoment B node5233 node5233Labels := by
  calc
    mixedMoment B raw6721 raw6721Labels = mixedMoment B raw6721step0 raw6721step0Labels := by
      have hz : ∀ j, raw6721 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6721step0 = (fun i j => raw6721 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6721step0 raw6721; decide +kernel
      have hl : raw6721step0Labels = raw6721Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6721 raw6721Labels permutation346 hz
    mixedMoment B raw6721step0 raw6721step0Labels = mixedMoment B raw6721step1 raw6721step1Labels := by
      have ha : raw6721step1 = (fun i j => raw6721step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6721step1 raw6721step0; decide +kernel
      have hl : raw6721step1Labels = raw6721step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6721step0 raw6721step0Labels permutation32 permutation6
    mixedMoment B raw6721step1 raw6721step1Labels = mixedMoment B raw6721step2 raw6721step2Labels := by
      have ha : raw6721step2 = raw6721step1 := by apply Matrix.ext; unfold raw6721step2 raw6721step1; decide +kernel
      have hl : raw6721step1Labels = labelEmbedding9 ∘ raw6721step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6721step1 raw6721step1Labels raw6721step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5233 node5233Labels := by rfl

def raw6722 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw6722Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6722step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw6722step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw6722step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw6722step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6722 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6722 raw6722Labels = mixedMoment B node5244 node5244Labels := by
  calc
    mixedMoment B raw6722 raw6722Labels = mixedMoment B raw6722step0 raw6722step0Labels := by
      have ha : raw6722step0 = (fun i j => raw6722 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6722step0 raw6722; decide +kernel
      have hl : raw6722step0Labels = raw6722Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6722 raw6722Labels permutation152 permutation6
    mixedMoment B raw6722step0 raw6722step0Labels = mixedMoment B raw6722step1 raw6722step1Labels := by
      have ha : raw6722step1 = raw6722step0 := by apply Matrix.ext; unfold raw6722step1 raw6722step0; decide +kernel
      have hl : raw6722step0Labels = labelEmbedding9 ∘ raw6722step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6722step0 raw6722step0Labels raw6722step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5244 node5244Labels := by rfl

def raw6723 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw6723Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6723step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw6723step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6723step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw6723step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw6723step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw6723step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw6723step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw6723step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6723 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6723 raw6723Labels = mixedMoment B node4810 node4810Labels := by
  calc
    mixedMoment B raw6723 raw6723Labels = mixedMoment B raw6723step0 raw6723step0Labels := by
      have hz : ∀ j, raw6723 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6723step0 = (fun i j => raw6723 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6723step0 raw6723; decide +kernel
      have hl : raw6723step0Labels = raw6723Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6723 raw6723Labels permutation346 hz
    mixedMoment B raw6723step0 raw6723step0Labels = mixedMoment B raw6723step1 raw6723step1Labels := by
      have ha : raw6723step1 = (fun i j => raw6723step0 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6723step1 raw6723step0; decide +kernel
      have hl : raw6723step1Labels = raw6723step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6723step0 raw6723step0Labels permutation34 permutation4
    mixedMoment B raw6723step1 raw6723step1Labels = mixedMoment B raw6723step2 raw6723step2Labels := by
      have ha : raw6723step2 = -raw6723step1 := by apply Matrix.ext; change ∀ i j, raw6723step2 i j = -(raw6723step1 i j); unfold raw6723step2 raw6723step1; decide +kernel
      have hl : raw6723step2Labels = raw6723step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6723step2 raw6723step2Labels = mixedMoment B raw6723step3 raw6723step3Labels := by
      have ha : raw6723step3 = raw6723step2 := by apply Matrix.ext; unfold raw6723step3 raw6723step2; decide +kernel
      have hl : raw6723step2Labels = labelEmbedding7 ∘ raw6723step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6723step2 raw6723step2Labels raw6723step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4810 node4810Labels := by rfl

def raw6724 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw6724Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6724step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![2, -2, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw6724step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6724step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw6724step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw6724step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw6724step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6724 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6724 raw6724Labels = mixedMoment B node5232 node5232Labels := by
  calc
    mixedMoment B raw6724 raw6724Labels = mixedMoment B raw6724step0 raw6724step0Labels := by
      have hz : ∀ j, raw6724 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6724step0 = (fun i j => raw6724 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6724step0 raw6724; decide +kernel
      have hl : raw6724step0Labels = raw6724Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6724 raw6724Labels permutation346 hz
    mixedMoment B raw6724step0 raw6724step0Labels = mixedMoment B raw6724step1 raw6724step1Labels := by
      have ha : raw6724step1 = (fun i j => raw6724step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6724step1 raw6724step0; decide +kernel
      have hl : raw6724step1Labels = raw6724step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6724step0 raw6724step0Labels permutation32 permutation6
    mixedMoment B raw6724step1 raw6724step1Labels = mixedMoment B raw6724step2 raw6724step2Labels := by
      have ha : raw6724step2 = raw6724step1 := by apply Matrix.ext; unfold raw6724step2 raw6724step1; decide +kernel
      have hl : raw6724step1Labels = labelEmbedding9 ∘ raw6724step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6724step1 raw6724step1Labels raw6724step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5232 node5232Labels := by rfl

def raw6725 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw6725Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6725step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw6725step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw6725step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw6725step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6725 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6725 raw6725Labels = mixedMoment B node5243 node5243Labels := by
  calc
    mixedMoment B raw6725 raw6725Labels = mixedMoment B raw6725step0 raw6725step0Labels := by
      have ha : raw6725step0 = (fun i j => raw6725 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6725step0 raw6725; decide +kernel
      have hl : raw6725step0Labels = raw6725Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6725 raw6725Labels permutation152 permutation6
    mixedMoment B raw6725step0 raw6725step0Labels = mixedMoment B raw6725step1 raw6725step1Labels := by
      have ha : raw6725step1 = raw6725step0 := by apply Matrix.ext; unfold raw6725step1 raw6725step0; decide +kernel
      have hl : raw6725step0Labels = labelEmbedding9 ∘ raw6725step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6725step0 raw6725step0Labels raw6725step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5243 node5243Labels := by rfl

def raw6726 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw6726Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6726step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw6726step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6726step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw6726step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw6726step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw6726step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6726 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6726 raw6726Labels = mixedMoment B node5258 node5258Labels := by
  calc
    mixedMoment B raw6726 raw6726Labels = mixedMoment B raw6726step0 raw6726step0Labels := by
      have hz : ∀ j, raw6726 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6726step0 = (fun i j => raw6726 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6726step0 raw6726; decide +kernel
      have hl : raw6726step0Labels = raw6726Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6726 raw6726Labels permutation346 hz
    mixedMoment B raw6726step0 raw6726step0Labels = mixedMoment B raw6726step1 raw6726step1Labels := by
      have ha : raw6726step1 = (fun i j => raw6726step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6726step1 raw6726step0; decide +kernel
      have hl : raw6726step1Labels = raw6726step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6726step0 raw6726step0Labels permutation32 permutation6
    mixedMoment B raw6726step1 raw6726step1Labels = mixedMoment B raw6726step2 raw6726step2Labels := by
      have ha : raw6726step2 = raw6726step1 := by apply Matrix.ext; unfold raw6726step2 raw6726step1; decide +kernel
      have hl : raw6726step1Labels = labelEmbedding9 ∘ raw6726step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6726step1 raw6726step1Labels raw6726step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5258 node5258Labels := by rfl

def raw6727 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw6727Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6727step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw6727step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6727step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw6727step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw6727step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw6727step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6727 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6727 raw6727Labels = mixedMoment B node5264 node5264Labels := by
  calc
    mixedMoment B raw6727 raw6727Labels = mixedMoment B raw6727step0 raw6727step0Labels := by
      have hz : ∀ j, raw6727 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6727step0 = (fun i j => raw6727 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6727step0 raw6727; decide +kernel
      have hl : raw6727step0Labels = raw6727Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6727 raw6727Labels permutation346 hz
    mixedMoment B raw6727step0 raw6727step0Labels = mixedMoment B raw6727step1 raw6727step1Labels := by
      have ha : raw6727step1 = (fun i j => raw6727step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6727step1 raw6727step0; decide +kernel
      have hl : raw6727step1Labels = raw6727step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6727step0 raw6727step0Labels permutation32 permutation6
    mixedMoment B raw6727step1 raw6727step1Labels = mixedMoment B raw6727step2 raw6727step2Labels := by
      have ha : raw6727step2 = raw6727step1 := by apply Matrix.ext; unfold raw6727step2 raw6727step1; decide +kernel
      have hl : raw6727step1Labels = labelEmbedding9 ∘ raw6727step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6727step1 raw6727step1Labels raw6727step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5264 node5264Labels := by rfl

def raw6728 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-2, 2, 0], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6728Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6728step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-2, 2, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6728step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6728step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6728step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6728 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6728 raw6728Labels = mixedMoment B node3044 node3044Labels := by
  calc
    mixedMoment B raw6728 raw6728Labels = mixedMoment B raw6728step0 raw6728step0Labels := by
      have hz : ∀ j, raw6728 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6728step0 = (fun i j => raw6728 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6728step0 raw6728; decide +kernel
      have hl : raw6728step0Labels = raw6728Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6728 raw6728Labels permutation346 hz
    mixedMoment B raw6728step0 raw6728step0Labels = mixedMoment B raw6728step1 raw6728step1Labels := by
      have ha : raw6728step1 = (fun i j => raw6728step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6728step1 raw6728step0; decide +kernel
      have hl : raw6728step1Labels = raw6728step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6728step0 raw6728step0Labels permutation32 permutation6
    _ = mixedMoment B node3044 node3044Labels := by rfl

def raw6729 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6729Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6729step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6729step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6729 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6729 raw6729Labels = mixedMoment B node3068 node3068Labels := by
  calc
    mixedMoment B raw6729 raw6729Labels = mixedMoment B raw6729step0 raw6729step0Labels := by
      have ha : raw6729step0 = (fun i j => raw6729 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6729step0 raw6729; decide +kernel
      have hl : raw6729step0Labels = raw6729Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6729 raw6729Labels permutation152 permutation6
    _ = mixedMoment B node3068 node3068Labels := by rfl

def raw6730 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6730Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6730step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6730step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6730step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw6730step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6730 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6730 raw6730Labels = mixedMoment B node3088 node3088Labels := by
  calc
    mixedMoment B raw6730 raw6730Labels = mixedMoment B raw6730step0 raw6730step0Labels := by
      have hz : ∀ j, raw6730 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6730step0 = (fun i j => raw6730 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6730step0 raw6730; decide +kernel
      have hl : raw6730step0Labels = raw6730Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6730 raw6730Labels permutation346 hz
    mixedMoment B raw6730step0 raw6730step0Labels = mixedMoment B raw6730step1 raw6730step1Labels := by
      have ha : raw6730step1 = (fun i j => raw6730step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6730step1 raw6730step0; decide +kernel
      have hl : raw6730step1Labels = raw6730step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6730step0 raw6730step0Labels permutation32 permutation6
    _ = mixedMoment B node3088 node3088Labels := by rfl

def raw6731 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw6731Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6731step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw6731step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6731step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw6731step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6731 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6731 raw6731Labels = mixedMoment B node3092 node3092Labels := by
  calc
    mixedMoment B raw6731 raw6731Labels = mixedMoment B raw6731step0 raw6731step0Labels := by
      have hz : ∀ j, raw6731 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6731step0 = (fun i j => raw6731 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6731step0 raw6731; decide +kernel
      have hl : raw6731step0Labels = raw6731Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6731 raw6731Labels permutation346 hz
    mixedMoment B raw6731step0 raw6731step0Labels = mixedMoment B raw6731step1 raw6731step1Labels := by
      have ha : raw6731step1 = (fun i j => raw6731step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6731step1 raw6731step0; decide +kernel
      have hl : raw6731step1Labels = raw6731step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6731step0 raw6731step0Labels permutation32 permutation6
    _ = mixedMoment B node3092 node3092Labels := by rfl

def raw6732 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw6732Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6732step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw6732step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6732step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw6732step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6732 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6732 raw6732Labels = mixedMoment B node3094 node3094Labels := by
  calc
    mixedMoment B raw6732 raw6732Labels = mixedMoment B raw6732step0 raw6732step0Labels := by
      have hz : ∀ j, raw6732 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6732step0 = (fun i j => raw6732 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6732step0 raw6732; decide +kernel
      have hl : raw6732step0Labels = raw6732Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6732 raw6732Labels permutation346 hz
    mixedMoment B raw6732step0 raw6732step0Labels = mixedMoment B raw6732step1 raw6732step1Labels := by
      have ha : raw6732step1 = (fun i j => raw6732step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6732step1 raw6732step0; decide +kernel
      have hl : raw6732step1Labels = raw6732step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6732step0 raw6732step0Labels permutation32 permutation6
    _ = mixedMoment B node3094 node3094Labels := by rfl

def raw6733 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6733Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6733step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6733step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6733step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6733step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6733step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6733step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6733 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6733 raw6733Labels = mixedMoment B node2278 node2278Labels := by
  calc
    mixedMoment B raw6733 raw6733Labels = mixedMoment B raw6733step0 raw6733step0Labels := by
      have hz : ∀ j, raw6733 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6733step0 = (fun i j => raw6733 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6733step0 raw6733; decide +kernel
      have hl : raw6733step0Labels = raw6733Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6733 raw6733Labels permutation346 hz
    mixedMoment B raw6733step0 raw6733step0Labels = mixedMoment B raw6733step1 raw6733step1Labels := by
      have hz : ∀ j, raw6733step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw6733step1 = (fun i j => raw6733step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw6733step1 raw6733step0; decide +kernel
      have hl : raw6733step1Labels = raw6733step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6733step0 raw6733step0Labels permutation56 hz
    mixedMoment B raw6733step1 raw6733step1Labels = mixedMoment B raw6733step2 raw6733step2Labels := by
      have ha : raw6733step2 = (fun i j => raw6733step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6733step2 raw6733step1; decide +kernel
      have hl : raw6733step2Labels = raw6733step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6733step1 raw6733step1Labels permutation8 permutation6
    _ = mixedMoment B node2278 node2278Labels := by rfl

def raw6734 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6734Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6734step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6734step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6734step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6734step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6734 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6734 raw6734Labels = mixedMoment B node2731 node2731Labels := by
  calc
    mixedMoment B raw6734 raw6734Labels = mixedMoment B raw6734step0 raw6734step0Labels := by
      have hz : ∀ j, raw6734 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw6734step0 = (fun i j => raw6734 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw6734step0 raw6734; decide +kernel
      have hl : raw6734step0Labels = raw6734Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6734 raw6734Labels permutation265 hz
    mixedMoment B raw6734step0 raw6734step0Labels = mixedMoment B raw6734step1 raw6734step1Labels := by
      have ha : raw6734step1 = (fun i j => raw6734step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6734step1 raw6734step0; decide +kernel
      have hl : raw6734step1Labels = raw6734step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6734step0 raw6734step0Labels permutation32 permutation6
    _ = mixedMoment B node2731 node2731Labels := by rfl

def raw6735 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6735Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6735step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6735step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6735step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6735step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6735step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw6735step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6735 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6735 raw6735Labels = mixedMoment B node2767 node2767Labels := by
  calc
    mixedMoment B raw6735 raw6735Labels = mixedMoment B raw6735step0 raw6735step0Labels := by
      have hz : ∀ j, raw6735 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6735step0 = (fun i j => raw6735 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6735step0 raw6735; decide +kernel
      have hl : raw6735step0Labels = raw6735Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6735 raw6735Labels permutation346 hz
    mixedMoment B raw6735step0 raw6735step0Labels = mixedMoment B raw6735step1 raw6735step1Labels := by
      have hz : ∀ j, raw6735step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw6735step1 = (fun i j => raw6735step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw6735step1 raw6735step0; decide +kernel
      have hl : raw6735step1Labels = raw6735step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6735step0 raw6735step0Labels permutation56 hz
    mixedMoment B raw6735step1 raw6735step1Labels = mixedMoment B raw6735step2 raw6735step2Labels := by
      have ha : raw6735step2 = (fun i j => raw6735step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6735step2 raw6735step1; decide +kernel
      have hl : raw6735step2Labels = raw6735step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6735step1 raw6735step1Labels permutation8 permutation6
    _ = mixedMoment B node2767 node2767Labels := by rfl

def raw6736 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw6736Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6736step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw6736step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6736step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw6736step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6736step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw6736step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6736 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6736 raw6736Labels = mixedMoment B node2774 node2774Labels := by
  calc
    mixedMoment B raw6736 raw6736Labels = mixedMoment B raw6736step0 raw6736step0Labels := by
      have hz : ∀ j, raw6736 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6736step0 = (fun i j => raw6736 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6736step0 raw6736; decide +kernel
      have hl : raw6736step0Labels = raw6736Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6736 raw6736Labels permutation346 hz
    mixedMoment B raw6736step0 raw6736step0Labels = mixedMoment B raw6736step1 raw6736step1Labels := by
      have hz : ∀ j, raw6736step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw6736step1 = (fun i j => raw6736step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw6736step1 raw6736step0; decide +kernel
      have hl : raw6736step1Labels = raw6736step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6736step0 raw6736step0Labels permutation56 hz
    mixedMoment B raw6736step1 raw6736step1Labels = mixedMoment B raw6736step2 raw6736step2Labels := by
      have ha : raw6736step2 = (fun i j => raw6736step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6736step2 raw6736step1; decide +kernel
      have hl : raw6736step2Labels = raw6736step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6736step1 raw6736step1Labels permutation8 permutation6
    _ = mixedMoment B node2774 node2774Labels := by rfl

def raw6737 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw6737Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6737step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw6737step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6737step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw6737step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6737step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw6737step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6737 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6737 raw6737Labels = mixedMoment B node2776 node2776Labels := by
  calc
    mixedMoment B raw6737 raw6737Labels = mixedMoment B raw6737step0 raw6737step0Labels := by
      have hz : ∀ j, raw6737 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6737step0 = (fun i j => raw6737 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6737step0 raw6737; decide +kernel
      have hl : raw6737step0Labels = raw6737Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6737 raw6737Labels permutation346 hz
    mixedMoment B raw6737step0 raw6737step0Labels = mixedMoment B raw6737step1 raw6737step1Labels := by
      have hz : ∀ j, raw6737step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw6737step1 = (fun i j => raw6737step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw6737step1 raw6737step0; decide +kernel
      have hl : raw6737step1Labels = raw6737step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6737step0 raw6737step0Labels permutation56 hz
    mixedMoment B raw6737step1 raw6737step1Labels = mixedMoment B raw6737step2 raw6737step2Labels := by
      have ha : raw6737step2 = (fun i j => raw6737step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6737step2 raw6737step1; decide +kernel
      have hl : raw6737step2Labels = raw6737step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6737step1 raw6737step1Labels permutation8 permutation6
    _ = mixedMoment B node2776 node2776Labels := by rfl

def raw6738 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6738Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6738step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6738step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6738 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6738 raw6738Labels = mixedMoment B node2195 node2195Labels := by
  calc
    mixedMoment B raw6738 raw6738Labels = mixedMoment B raw6738step0 raw6738step0Labels := by
      have ha : raw6738step0 = (fun i j => raw6738 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6738step0 raw6738; decide +kernel
      have hl : raw6738step0Labels = raw6738Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6738 raw6738Labels permutation152 permutation6
    _ = mixedMoment B node2195 node2195Labels := by rfl

def raw6739 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6739Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6739step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6739step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6739 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6739 raw6739Labels = mixedMoment B node2665 node2665Labels := by
  calc
    mixedMoment B raw6739 raw6739Labels = mixedMoment B raw6739step0 raw6739step0Labels := by
      have ha : raw6739step0 = (fun i j => raw6739 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6739step0 raw6739; decide +kernel
      have hl : raw6739step0Labels = raw6739Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6739 raw6739Labels permutation152 permutation6
    _ = mixedMoment B node2665 node2665Labels := by rfl

def raw6740 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6740Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6740step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw6740step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6740 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6740 raw6740Labels = mixedMoment B node2709 node2709Labels := by
  calc
    mixedMoment B raw6740 raw6740Labels = mixedMoment B raw6740step0 raw6740step0Labels := by
      have ha : raw6740step0 = (fun i j => raw6740 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6740step0 raw6740; decide +kernel
      have hl : raw6740step0Labels = raw6740Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6740 raw6740Labels permutation152 permutation6
    _ = mixedMoment B node2709 node2709Labels := by rfl

def raw6741 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw6741Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6741step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw6741step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6741 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6741 raw6741Labels = mixedMoment B node2713 node2713Labels := by
  calc
    mixedMoment B raw6741 raw6741Labels = mixedMoment B raw6741step0 raw6741step0Labels := by
      have ha : raw6741step0 = (fun i j => raw6741 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6741step0 raw6741; decide +kernel
      have hl : raw6741step0Labels = raw6741Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6741 raw6741Labels permutation152 permutation6
    _ = mixedMoment B node2713 node2713Labels := by rfl

def raw6742 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw6742Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6742step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw6742step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6742 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6742 raw6742Labels = mixedMoment B node2714 node2714Labels := by
  calc
    mixedMoment B raw6742 raw6742Labels = mixedMoment B raw6742step0 raw6742step0Labels := by
      have ha : raw6742step0 = (fun i j => raw6742 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6742step0 raw6742; decide +kernel
      have hl : raw6742step0Labels = raw6742Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6742 raw6742Labels permutation152 permutation6
    _ = mixedMoment B node2714 node2714Labels := by rfl

def raw6743 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![0, 0, 0], ![3, -3, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6743Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6743step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![3, -3, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6743step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6743step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]
def raw6743step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6743 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6743 raw6743Labels = mixedMoment B node2220 node2220Labels := by
  calc
    mixedMoment B raw6743 raw6743Labels = mixedMoment B raw6743step0 raw6743step0Labels := by
      have hz : ∀ j, raw6743 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6743step0 = (fun i j => raw6743 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6743step0 raw6743; decide +kernel
      have hl : raw6743step0Labels = raw6743Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6743 raw6743Labels permutation346 hz
    mixedMoment B raw6743step0 raw6743step0Labels = mixedMoment B raw6743step1 raw6743step1Labels := by
      have ha : raw6743step1 = (fun i j => raw6743step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6743step1 raw6743step0; decide +kernel
      have hl : raw6743step1Labels = raw6743step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6743step0 raw6743step0Labels permutation32 permutation6
    _ = mixedMoment B node2220 node2220Labels := by rfl

def raw6744 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![0, 0, 0], ![3, -3, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6744Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6744step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![3, -3, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6744step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6744step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![-1, 2, -1], ![-1, 1, 0], ![-2, 0, 2]]
def raw6744step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6744step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw6744step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6744 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6744 raw6744Labels = mixedMoment B node2128 node2128Labels := by
  calc
    mixedMoment B raw6744 raw6744Labels = mixedMoment B raw6744step0 raw6744step0Labels := by
      have hz : ∀ j, raw6744 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6744step0 = (fun i j => raw6744 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6744step0 raw6744; decide +kernel
      have hl : raw6744step0Labels = raw6744Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6744 raw6744Labels permutation346 hz
    mixedMoment B raw6744step0 raw6744step0Labels = mixedMoment B raw6744step1 raw6744step1Labels := by
      have ha : raw6744step1 = (fun i j => raw6744step0 (permutation85 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6744step1 raw6744step0; decide +kernel
      have hl : raw6744step1Labels = raw6744step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6744step0 raw6744step0Labels permutation85 permutation3
    mixedMoment B raw6744step1 raw6744step1Labels = mixedMoment B raw6744step2 raw6744step2Labels := by
      have ha : raw6744step2 = -raw6744step1 := by apply Matrix.ext; change ∀ i j, raw6744step2 i j = -(raw6744step1 i j); unfold raw6744step2 raw6744step1; decide +kernel
      have hl : raw6744step2Labels = raw6744step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2128 node2128Labels := by rfl

def raw6745 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 1, 0], ![3, -3, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6745Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6745step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw6745step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6745step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw6745step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6745 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6745 raw6745Labels = mixedMoment B node2127 node2127Labels := by
  calc
    mixedMoment B raw6745 raw6745Labels = mixedMoment B raw6745step0 raw6745step0Labels := by
      have ha : raw6745step0 = (fun i j => raw6745 (permutation449 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6745step0 raw6745; decide +kernel
      have hl : raw6745step0Labels = raw6745Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6745 raw6745Labels permutation449 permutation3
    mixedMoment B raw6745step0 raw6745step0Labels = mixedMoment B raw6745step1 raw6745step1Labels := by
      have ha : raw6745step1 = -raw6745step0 := by apply Matrix.ext; change ∀ i j, raw6745step1 i j = -(raw6745step0 i j); unfold raw6745step1 raw6745step0; decide +kernel
      have hl : raw6745step1Labels = raw6745step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2127 node2127Labels := by rfl

def raw6746 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![3, -3, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw6746Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6746step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![3, -3, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw6746step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6746step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![-1, 2, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw6746step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6746step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw6746step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6746 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6746 raw6746Labels = mixedMoment B node2129 node2129Labels := by
  calc
    mixedMoment B raw6746 raw6746Labels = mixedMoment B raw6746step0 raw6746step0Labels := by
      have hz : ∀ j, raw6746 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6746step0 = (fun i j => raw6746 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6746step0 raw6746; decide +kernel
      have hl : raw6746step0Labels = raw6746Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6746 raw6746Labels permutation346 hz
    mixedMoment B raw6746step0 raw6746step0Labels = mixedMoment B raw6746step1 raw6746step1Labels := by
      have ha : raw6746step1 = (fun i j => raw6746step0 (permutation84 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6746step1 raw6746step0; decide +kernel
      have hl : raw6746step1Labels = raw6746step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6746step0 raw6746step0Labels permutation84 permutation3
    mixedMoment B raw6746step1 raw6746step1Labels = mixedMoment B raw6746step2 raw6746step2Labels := by
      have ha : raw6746step2 = -raw6746step1 := by apply Matrix.ext; change ∀ i j, raw6746step2 i j = -(raw6746step1 i j); unfold raw6746step2 raw6746step1; decide +kernel
      have hl : raw6746step2Labels = raw6746step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2129 node2129Labels := by rfl

def raw6747 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![3, -3, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw6747Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6747step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![3, -3, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw6747step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6747step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw6747step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6747step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw6747step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6747 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6747 raw6747Labels = mixedMoment B node2133 node2133Labels := by
  calc
    mixedMoment B raw6747 raw6747Labels = mixedMoment B raw6747step0 raw6747step0Labels := by
      have hz : ∀ j, raw6747 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6747step0 = (fun i j => raw6747 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6747step0 raw6747; decide +kernel
      have hl : raw6747step0Labels = raw6747Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6747 raw6747Labels permutation346 hz
    mixedMoment B raw6747step0 raw6747step0Labels = mixedMoment B raw6747step1 raw6747step1Labels := by
      have ha : raw6747step1 = (fun i j => raw6747step0 (permutation82 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6747step1 raw6747step0; decide +kernel
      have hl : raw6747step1Labels = raw6747step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6747step0 raw6747step0Labels permutation82 permutation3
    mixedMoment B raw6747step1 raw6747step1Labels = mixedMoment B raw6747step2 raw6747step2Labels := by
      have ha : raw6747step2 = -raw6747step1 := by apply Matrix.ext; change ∀ i j, raw6747step2 i j = -(raw6747step1 i j); unfold raw6747step2 raw6747step1; decide +kernel
      have hl : raw6747step2Labels = raw6747step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2133 node2133Labels := by rfl

def raw6748 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw6748Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6748step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![2, -2, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw6748step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6748step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw6748step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6748 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6748 raw6748Labels = mixedMoment B node2216 node2216Labels := by
  calc
    mixedMoment B raw6748 raw6748Labels = mixedMoment B raw6748step0 raw6748step0Labels := by
      have hz : ∀ j, raw6748 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6748step0 = (fun i j => raw6748 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6748step0 raw6748; decide +kernel
      have hl : raw6748step0Labels = raw6748Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6748 raw6748Labels permutation346 hz
    mixedMoment B raw6748step0 raw6748step0Labels = mixedMoment B raw6748step1 raw6748step1Labels := by
      have ha : raw6748step1 = (fun i j => raw6748step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6748step1 raw6748step0; decide +kernel
      have hl : raw6748step1Labels = raw6748step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6748step0 raw6748step0Labels permutation32 permutation6
    _ = mixedMoment B node2216 node2216Labels := by rfl

def raw6749 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![0, 0, 0], ![2, -2, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw6749Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6749step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![2, -2, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw6749step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6749step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw6749step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6749 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6749 raw6749Labels = mixedMoment B node2678 node2678Labels := by
  calc
    mixedMoment B raw6749 raw6749Labels = mixedMoment B raw6749step0 raw6749step0Labels := by
      have hz : ∀ j, raw6749 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6749step0 = (fun i j => raw6749 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6749step0 raw6749; decide +kernel
      have hl : raw6749step0Labels = raw6749Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6749 raw6749Labels permutation346 hz
    mixedMoment B raw6749step0 raw6749step0Labels = mixedMoment B raw6749step1 raw6749step1Labels := by
      have ha : raw6749step1 = (fun i j => raw6749step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6749step1 raw6749step0; decide +kernel
      have hl : raw6749step1Labels = raw6749step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6749step0 raw6749step0Labels permutation32 permutation6
    _ = mixedMoment B node2678 node2678Labels := by rfl

def raw6750 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw6750Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6750step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw6750step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6750 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6750 raw6750Labels = mixedMoment B node2698 node2698Labels := by
  calc
    mixedMoment B raw6750 raw6750Labels = mixedMoment B raw6750step0 raw6750step0Labels := by
      have ha : raw6750step0 = (fun i j => raw6750 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6750step0 raw6750; decide +kernel
      have hl : raw6750step0Labels = raw6750Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6750 raw6750Labels permutation152 permutation6
    _ = mixedMoment B node2698 node2698Labels := by rfl

def raw6751 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw6751Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6751step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw6751step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6751step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw6751step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6751 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6751 raw6751Labels = mixedMoment B node2215 node2215Labels := by
  calc
    mixedMoment B raw6751 raw6751Labels = mixedMoment B raw6751step0 raw6751step0Labels := by
      have hz : ∀ j, raw6751 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6751step0 = (fun i j => raw6751 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6751step0 raw6751; decide +kernel
      have hl : raw6751step0Labels = raw6751Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6751 raw6751Labels permutation346 hz
    mixedMoment B raw6751step0 raw6751step0Labels = mixedMoment B raw6751step1 raw6751step1Labels := by
      have ha : raw6751step1 = (fun i j => raw6751step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6751step1 raw6751step0; decide +kernel
      have hl : raw6751step1Labels = raw6751step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6751step0 raw6751step0Labels permutation32 permutation6
    _ = mixedMoment B node2215 node2215Labels := by rfl

def raw6752 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw6752Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6752step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![2, -2, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw6752step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6752step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw6752step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6752 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6752 raw6752Labels = mixedMoment B node2677 node2677Labels := by
  calc
    mixedMoment B raw6752 raw6752Labels = mixedMoment B raw6752step0 raw6752step0Labels := by
      have hz : ∀ j, raw6752 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6752step0 = (fun i j => raw6752 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6752step0 raw6752; decide +kernel
      have hl : raw6752step0Labels = raw6752Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6752 raw6752Labels permutation346 hz
    mixedMoment B raw6752step0 raw6752step0Labels = mixedMoment B raw6752step1 raw6752step1Labels := by
      have ha : raw6752step1 = (fun i j => raw6752step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6752step1 raw6752step0; decide +kernel
      have hl : raw6752step1Labels = raw6752step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6752step0 raw6752step0Labels permutation32 permutation6
    _ = mixedMoment B node2677 node2677Labels := by rfl

def raw6753 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw6753Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6753step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw6753step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6753 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6753 raw6753Labels = mixedMoment B node2697 node2697Labels := by
  calc
    mixedMoment B raw6753 raw6753Labels = mixedMoment B raw6753step0 raw6753step0Labels := by
      have ha : raw6753step0 = (fun i j => raw6753 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6753step0 raw6753; decide +kernel
      have hl : raw6753step0Labels = raw6753Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6753 raw6753Labels permutation152 permutation6
    _ = mixedMoment B node2697 node2697Labels := by rfl

def raw6754 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw6754Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6754step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw6754step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6754step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw6754step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6754 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6754 raw6754Labels = mixedMoment B node2722 node2722Labels := by
  calc
    mixedMoment B raw6754 raw6754Labels = mixedMoment B raw6754step0 raw6754step0Labels := by
      have hz : ∀ j, raw6754 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6754step0 = (fun i j => raw6754 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6754step0 raw6754; decide +kernel
      have hl : raw6754step0Labels = raw6754Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6754 raw6754Labels permutation346 hz
    mixedMoment B raw6754step0 raw6754step0Labels = mixedMoment B raw6754step1 raw6754step1Labels := by
      have ha : raw6754step1 = (fun i j => raw6754step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6754step1 raw6754step0; decide +kernel
      have hl : raw6754step1Labels = raw6754step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6754step0 raw6754step0Labels permutation32 permutation6
    _ = mixedMoment B node2722 node2722Labels := by rfl

def raw6755 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw6755Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6755step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw6755step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6755step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw6755step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6755 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6755 raw6755Labels = mixedMoment B node2729 node2729Labels := by
  calc
    mixedMoment B raw6755 raw6755Labels = mixedMoment B raw6755step0 raw6755step0Labels := by
      have hz : ∀ j, raw6755 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6755step0 = (fun i j => raw6755 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6755step0 raw6755; decide +kernel
      have hl : raw6755step0Labels = raw6755Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6755 raw6755Labels permutation346 hz
    mixedMoment B raw6755step0 raw6755step0Labels = mixedMoment B raw6755step1 raw6755step1Labels := by
      have ha : raw6755step1 = (fun i j => raw6755step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6755step1 raw6755step0; decide +kernel
      have hl : raw6755step1Labels = raw6755step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6755step0 raw6755step0Labels permutation32 permutation6
    _ = mixedMoment B node2729 node2729Labels := by rfl

def raw6756 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-2, 2, 0], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6756Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6756step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-2, 2, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6756step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6756step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw6756step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6756step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw6756step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6756 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6756 raw6756Labels = mixedMoment B node2678 node2678Labels := by
  calc
    mixedMoment B raw6756 raw6756Labels = mixedMoment B raw6756step0 raw6756step0Labels := by
      have hz : ∀ j, raw6756 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6756step0 = (fun i j => raw6756 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6756step0 raw6756; decide +kernel
      have hl : raw6756step0Labels = raw6756Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6756 raw6756Labels permutation346 hz
    mixedMoment B raw6756step0 raw6756step0Labels = mixedMoment B raw6756step1 raw6756step1Labels := by
      have ha : raw6756step1 = (fun i j => raw6756step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw6756step1 raw6756step0; decide +kernel
      have hl : raw6756step1Labels = raw6756step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6756step0 raw6756step0Labels permutation38 permutation7
    mixedMoment B raw6756step1 raw6756step1Labels = mixedMoment B raw6756step2 raw6756step2Labels := by
      have ha : raw6756step2 = raw6756step1 := by apply Matrix.ext; unfold raw6756step2 raw6756step1; decide +kernel
      have hl : raw6756step1Labels = labelEmbedding1 ∘ raw6756step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6756step1 raw6756step1Labels raw6756step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2678 node2678Labels := by rfl

def raw6757 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6757Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6757step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw6757step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6757step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw6757step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6757 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6757 raw6757Labels = mixedMoment B node2662 node2662Labels := by
  calc
    mixedMoment B raw6757 raw6757Labels = mixedMoment B raw6757step0 raw6757step0Labels := by
      have ha : raw6757step0 = (fun i j => raw6757 (permutation200 i) (permutation7 j)) := by apply Matrix.ext; unfold raw6757step0 raw6757; decide +kernel
      have hl : raw6757step0Labels = raw6757Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6757 raw6757Labels permutation200 permutation7
    mixedMoment B raw6757step0 raw6757step0Labels = mixedMoment B raw6757step1 raw6757step1Labels := by
      have ha : raw6757step1 = raw6757step0 := by apply Matrix.ext; unfold raw6757step1 raw6757step0; decide +kernel
      have hl : raw6757step0Labels = labelEmbedding1 ∘ raw6757step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6757step0 raw6757step0Labels raw6757step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2662 node2662Labels := by rfl

def raw6758 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6758Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6758step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6758step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6758step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw6758step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6758step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw6758step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6758 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6758 raw6758Labels = mixedMoment B node2723 node2723Labels := by
  calc
    mixedMoment B raw6758 raw6758Labels = mixedMoment B raw6758step0 raw6758step0Labels := by
      have hz : ∀ j, raw6758 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6758step0 = (fun i j => raw6758 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6758step0 raw6758; decide +kernel
      have hl : raw6758step0Labels = raw6758Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6758 raw6758Labels permutation346 hz
    mixedMoment B raw6758step0 raw6758step0Labels = mixedMoment B raw6758step1 raw6758step1Labels := by
      have ha : raw6758step1 = (fun i j => raw6758step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw6758step1 raw6758step0; decide +kernel
      have hl : raw6758step1Labels = raw6758step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6758step0 raw6758step0Labels permutation38 permutation7
    mixedMoment B raw6758step1 raw6758step1Labels = mixedMoment B raw6758step2 raw6758step2Labels := by
      have ha : raw6758step2 = raw6758step1 := by apply Matrix.ext; unfold raw6758step2 raw6758step1; decide +kernel
      have hl : raw6758step1Labels = labelEmbedding1 ∘ raw6758step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6758step1 raw6758step1Labels raw6758step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2723 node2723Labels := by rfl

def raw6759 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw6759Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6759step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw6759step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6759step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw6759step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6759step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw6759step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6759 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6759 raw6759Labels = mixedMoment B node2673 node2673Labels := by
  calc
    mixedMoment B raw6759 raw6759Labels = mixedMoment B raw6759step0 raw6759step0Labels := by
      have hz : ∀ j, raw6759 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6759step0 = (fun i j => raw6759 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6759step0 raw6759; decide +kernel
      have hl : raw6759step0Labels = raw6759Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6759 raw6759Labels permutation346 hz
    mixedMoment B raw6759step0 raw6759step0Labels = mixedMoment B raw6759step1 raw6759step1Labels := by
      have ha : raw6759step1 = (fun i j => raw6759step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw6759step1 raw6759step0; decide +kernel
      have hl : raw6759step1Labels = raw6759step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6759step0 raw6759step0Labels permutation38 permutation7
    mixedMoment B raw6759step1 raw6759step1Labels = mixedMoment B raw6759step2 raw6759step2Labels := by
      have ha : raw6759step2 = raw6759step1 := by apply Matrix.ext; unfold raw6759step2 raw6759step1; decide +kernel
      have hl : raw6759step1Labels = labelEmbedding1 ∘ raw6759step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6759step1 raw6759step1Labels raw6759step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2673 node2673Labels := by rfl

def raw6760 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw6760Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6760step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw6760step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6760step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw6760step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6760step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw6760step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6760 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6760 raw6760Labels = mixedMoment B node2672 node2672Labels := by
  calc
    mixedMoment B raw6760 raw6760Labels = mixedMoment B raw6760step0 raw6760step0Labels := by
      have hz : ∀ j, raw6760 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6760step0 = (fun i j => raw6760 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6760step0 raw6760; decide +kernel
      have hl : raw6760step0Labels = raw6760Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6760 raw6760Labels permutation346 hz
    mixedMoment B raw6760step0 raw6760step0Labels = mixedMoment B raw6760step1 raw6760step1Labels := by
      have ha : raw6760step1 = (fun i j => raw6760step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw6760step1 raw6760step0; decide +kernel
      have hl : raw6760step1Labels = raw6760step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6760step0 raw6760step0Labels permutation38 permutation7
    mixedMoment B raw6760step1 raw6760step1Labels = mixedMoment B raw6760step2 raw6760step2Labels := by
      have ha : raw6760step2 = raw6760step1 := by apply Matrix.ext; unfold raw6760step2 raw6760step1; decide +kernel
      have hl : raw6760step1Labels = labelEmbedding1 ∘ raw6760step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6760step1 raw6760step1Labels raw6760step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2672 node2672Labels := by rfl

def raw6761 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6761Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6761step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6761step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6761step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6761step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6761step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw6761step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6761step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw6761step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6761 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6761 raw6761Labels = mixedMoment B node3225 node3225Labels := by
  calc
    mixedMoment B raw6761 raw6761Labels = mixedMoment B raw6761step0 raw6761step0Labels := by
      have hz : ∀ j, raw6761 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6761step0 = (fun i j => raw6761 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6761step0 raw6761; decide +kernel
      have hl : raw6761step0Labels = raw6761Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6761 raw6761Labels permutation346 hz
    mixedMoment B raw6761step0 raw6761step0Labels = mixedMoment B raw6761step1 raw6761step1Labels := by
      have hz : ∀ j, raw6761step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw6761step1 = (fun i j => raw6761step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw6761step1 raw6761step0; decide +kernel
      have hl : raw6761step1Labels = raw6761step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6761step0 raw6761step0Labels permutation56 hz
    mixedMoment B raw6761step1 raw6761step1Labels = mixedMoment B raw6761step2 raw6761step2Labels := by
      have ha : raw6761step2 = (fun i j => raw6761step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw6761step2 raw6761step1; decide +kernel
      have hl : raw6761step2Labels = raw6761step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6761step1 raw6761step1Labels permutation8 permutation7
    mixedMoment B raw6761step2 raw6761step2Labels = mixedMoment B raw6761step3 raw6761step3Labels := by
      have ha : raw6761step3 = raw6761step2 := by apply Matrix.ext; unfold raw6761step3 raw6761step2; decide +kernel
      have hl : raw6761step2Labels = labelEmbedding1 ∘ raw6761step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6761step2 raw6761step2Labels raw6761step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3225 node3225Labels := by rfl

def raw6762 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6762Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6762step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6762step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6762step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw6762step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6762step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw6762step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6762 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6762 raw6762Labels = mixedMoment B node3039 node3039Labels := by
  calc
    mixedMoment B raw6762 raw6762Labels = mixedMoment B raw6762step0 raw6762step0Labels := by
      have hz : ∀ j, raw6762 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw6762step0 = (fun i j => raw6762 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw6762step0 raw6762; decide +kernel
      have hl : raw6762step0Labels = raw6762Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6762 raw6762Labels permutation265 hz
    mixedMoment B raw6762step0 raw6762step0Labels = mixedMoment B raw6762step1 raw6762step1Labels := by
      have ha : raw6762step1 = (fun i j => raw6762step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw6762step1 raw6762step0; decide +kernel
      have hl : raw6762step1Labels = raw6762step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6762step0 raw6762step0Labels permutation38 permutation7
    mixedMoment B raw6762step1 raw6762step1Labels = mixedMoment B raw6762step2 raw6762step2Labels := by
      have ha : raw6762step2 = raw6762step1 := by apply Matrix.ext; unfold raw6762step2 raw6762step1; decide +kernel
      have hl : raw6762step1Labels = labelEmbedding1 ∘ raw6762step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6762step1 raw6762step1Labels raw6762step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3039 node3039Labels := by rfl

def raw6763 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6763Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6763step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6763step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6763step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6763step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6763step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw6763step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6763step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw6763step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6763 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6763 raw6763Labels = mixedMoment B node3102 node3102Labels := by
  calc
    mixedMoment B raw6763 raw6763Labels = mixedMoment B raw6763step0 raw6763step0Labels := by
      have hz : ∀ j, raw6763 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6763step0 = (fun i j => raw6763 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6763step0 raw6763; decide +kernel
      have hl : raw6763step0Labels = raw6763Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6763 raw6763Labels permutation346 hz
    mixedMoment B raw6763step0 raw6763step0Labels = mixedMoment B raw6763step1 raw6763step1Labels := by
      have hz : ∀ j, raw6763step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw6763step1 = (fun i j => raw6763step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw6763step1 raw6763step0; decide +kernel
      have hl : raw6763step1Labels = raw6763step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6763step0 raw6763step0Labels permutation56 hz
    mixedMoment B raw6763step1 raw6763step1Labels = mixedMoment B raw6763step2 raw6763step2Labels := by
      have ha : raw6763step2 = (fun i j => raw6763step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw6763step2 raw6763step1; decide +kernel
      have hl : raw6763step2Labels = raw6763step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6763step1 raw6763step1Labels permutation8 permutation7
    mixedMoment B raw6763step2 raw6763step2Labels = mixedMoment B raw6763step3 raw6763step3Labels := by
      have ha : raw6763step3 = raw6763step2 := by apply Matrix.ext; unfold raw6763step3 raw6763step2; decide +kernel
      have hl : raw6763step2Labels = labelEmbedding1 ∘ raw6763step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6763step2 raw6763step2Labels raw6763step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3102 node3102Labels := by rfl

def raw6764 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw6764Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6764step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw6764step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6764step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw6764step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6764step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw6764step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6764step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw6764step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6764 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6764 raw6764Labels = mixedMoment B node3055 node3055Labels := by
  calc
    mixedMoment B raw6764 raw6764Labels = mixedMoment B raw6764step0 raw6764step0Labels := by
      have hz : ∀ j, raw6764 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6764step0 = (fun i j => raw6764 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6764step0 raw6764; decide +kernel
      have hl : raw6764step0Labels = raw6764Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6764 raw6764Labels permutation346 hz
    mixedMoment B raw6764step0 raw6764step0Labels = mixedMoment B raw6764step1 raw6764step1Labels := by
      have hz : ∀ j, raw6764step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw6764step1 = (fun i j => raw6764step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw6764step1 raw6764step0; decide +kernel
      have hl : raw6764step1Labels = raw6764step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6764step0 raw6764step0Labels permutation56 hz
    mixedMoment B raw6764step1 raw6764step1Labels = mixedMoment B raw6764step2 raw6764step2Labels := by
      have ha : raw6764step2 = (fun i j => raw6764step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw6764step2 raw6764step1; decide +kernel
      have hl : raw6764step2Labels = raw6764step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6764step1 raw6764step1Labels permutation8 permutation7
    mixedMoment B raw6764step2 raw6764step2Labels = mixedMoment B raw6764step3 raw6764step3Labels := by
      have ha : raw6764step3 = raw6764step2 := by apply Matrix.ext; unfold raw6764step3 raw6764step2; decide +kernel
      have hl : raw6764step2Labels = labelEmbedding1 ∘ raw6764step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6764step2 raw6764step2Labels raw6764step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3055 node3055Labels := by rfl

def raw6765 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw6765Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6765step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw6765step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6765step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw6765step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6765step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw6765step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6765step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw6765step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6765 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6765 raw6765Labels = mixedMoment B node3054 node3054Labels := by
  calc
    mixedMoment B raw6765 raw6765Labels = mixedMoment B raw6765step0 raw6765step0Labels := by
      have hz : ∀ j, raw6765 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6765step0 = (fun i j => raw6765 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6765step0 raw6765; decide +kernel
      have hl : raw6765step0Labels = raw6765Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6765 raw6765Labels permutation346 hz
    mixedMoment B raw6765step0 raw6765step0Labels = mixedMoment B raw6765step1 raw6765step1Labels := by
      have hz : ∀ j, raw6765step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw6765step1 = (fun i j => raw6765step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw6765step1 raw6765step0; decide +kernel
      have hl : raw6765step1Labels = raw6765step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6765step0 raw6765step0Labels permutation56 hz
    mixedMoment B raw6765step1 raw6765step1Labels = mixedMoment B raw6765step2 raw6765step2Labels := by
      have ha : raw6765step2 = (fun i j => raw6765step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw6765step2 raw6765step1; decide +kernel
      have hl : raw6765step2Labels = raw6765step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6765step1 raw6765step1Labels permutation8 permutation7
    mixedMoment B raw6765step2 raw6765step2Labels = mixedMoment B raw6765step3 raw6765step3Labels := by
      have ha : raw6765step3 = raw6765step2 := by apply Matrix.ext; unfold raw6765step3 raw6765step2; decide +kernel
      have hl : raw6765step2Labels = labelEmbedding1 ∘ raw6765step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6765step2 raw6765step2Labels raw6765step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3054 node3054Labels := by rfl

def raw6766 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6766Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6766step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![1, 0, -1], ![0, 1, -1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw6766step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6766step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw6766step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6766step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw6766step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6766 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6766 raw6766Labels = mixedMoment B node3202 node3202Labels := by
  calc
    mixedMoment B raw6766 raw6766Labels = mixedMoment B raw6766step0 raw6766step0Labels := by
      have ha : raw6766step0 = (fun i j => raw6766 (permutation168 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6766step0 raw6766; decide +kernel
      have hl : raw6766step0Labels = raw6766Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6766 raw6766Labels permutation168 permutation5
    mixedMoment B raw6766step0 raw6766step0Labels = mixedMoment B raw6766step1 raw6766step1Labels := by
      have ha : raw6766step1 = -raw6766step0 := by apply Matrix.ext; change ∀ i j, raw6766step1 i j = -(raw6766step0 i j); unfold raw6766step1 raw6766step0; decide +kernel
      have hl : raw6766step1Labels = raw6766step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6766step1 raw6766step1Labels = mixedMoment B raw6766step2 raw6766step2Labels := by
      have ha : raw6766step2 = raw6766step1 := by apply Matrix.ext; unfold raw6766step2 raw6766step1; decide +kernel
      have hl : raw6766step1Labels = labelEmbedding1 ∘ raw6766step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6766step1 raw6766step1Labels raw6766step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3202 node3202Labels := by rfl

def raw6767 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6767Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6767step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw6767step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6767step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw6767step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6767 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6767 raw6767Labels = mixedMoment B node3019 node3019Labels := by
  calc
    mixedMoment B raw6767 raw6767Labels = mixedMoment B raw6767step0 raw6767step0Labels := by
      have ha : raw6767step0 = (fun i j => raw6767 (permutation206 i) (permutation7 j)) := by apply Matrix.ext; unfold raw6767step0 raw6767; decide +kernel
      have hl : raw6767step0Labels = raw6767Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6767 raw6767Labels permutation206 permutation7
    mixedMoment B raw6767step0 raw6767step0Labels = mixedMoment B raw6767step1 raw6767step1Labels := by
      have ha : raw6767step1 = raw6767step0 := by apply Matrix.ext; unfold raw6767step1 raw6767step0; decide +kernel
      have hl : raw6767step0Labels = labelEmbedding1 ∘ raw6767step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6767step0 raw6767step0Labels raw6767step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3019 node3019Labels := by rfl

def raw6768 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6768Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6768step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw6768step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6768step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw6768step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6768 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6768 raw6768Labels = mixedMoment B node3065 node3065Labels := by
  calc
    mixedMoment B raw6768 raw6768Labels = mixedMoment B raw6768step0 raw6768step0Labels := by
      have ha : raw6768step0 = (fun i j => raw6768 (permutation182 i) (permutation7 j)) := by apply Matrix.ext; unfold raw6768step0 raw6768; decide +kernel
      have hl : raw6768step0Labels = raw6768Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6768 raw6768Labels permutation182 permutation7
    mixedMoment B raw6768step0 raw6768step0Labels = mixedMoment B raw6768step1 raw6768step1Labels := by
      have ha : raw6768step1 = raw6768step0 := by apply Matrix.ext; unfold raw6768step1 raw6768step0; decide +kernel
      have hl : raw6768step0Labels = labelEmbedding1 ∘ raw6768step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6768step0 raw6768step0Labels raw6768step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3065 node3065Labels := by rfl

def raw6769 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw6769Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6769step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw6769step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6769step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw6769step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6769 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6769 raw6769Labels = mixedMoment B node3017 node3017Labels := by
  calc
    mixedMoment B raw6769 raw6769Labels = mixedMoment B raw6769step0 raw6769step0Labels := by
      have ha : raw6769step0 = (fun i j => raw6769 (permutation206 i) (permutation7 j)) := by apply Matrix.ext; unfold raw6769step0 raw6769; decide +kernel
      have hl : raw6769step0Labels = raw6769Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6769 raw6769Labels permutation206 permutation7
    mixedMoment B raw6769step0 raw6769step0Labels = mixedMoment B raw6769step1 raw6769step1Labels := by
      have ha : raw6769step1 = raw6769step0 := by apply Matrix.ext; unfold raw6769step1 raw6769step0; decide +kernel
      have hl : raw6769step0Labels = labelEmbedding1 ∘ raw6769step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6769step0 raw6769step0Labels raw6769step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3017 node3017Labels := by rfl

def raw6770 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw6770Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6770step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw6770step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6770step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw6770step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6770 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6770 raw6770Labels = mixedMoment B node3016 node3016Labels := by
  calc
    mixedMoment B raw6770 raw6770Labels = mixedMoment B raw6770step0 raw6770step0Labels := by
      have ha : raw6770step0 = (fun i j => raw6770 (permutation206 i) (permutation7 j)) := by apply Matrix.ext; unfold raw6770step0 raw6770; decide +kernel
      have hl : raw6770step0Labels = raw6770Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6770 raw6770Labels permutation206 permutation7
    mixedMoment B raw6770step0 raw6770step0Labels = mixedMoment B raw6770step1 raw6770step1Labels := by
      have ha : raw6770step1 = raw6770step0 := by apply Matrix.ext; unfold raw6770step1 raw6770step0; decide +kernel
      have hl : raw6770step0Labels = labelEmbedding1 ∘ raw6770step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6770step0 raw6770step0Labels raw6770step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3016 node3016Labels := by rfl

def raw6771 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![0, 0, 0], ![3, -3, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6771Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6771step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![3, -3, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6771step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6771step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw6771step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6771step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw6771step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6771 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6771 raw6771Labels = mixedMoment B node2092 node2092Labels := by
  calc
    mixedMoment B raw6771 raw6771Labels = mixedMoment B raw6771step0 raw6771step0Labels := by
      have hz : ∀ j, raw6771 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6771step0 = (fun i j => raw6771 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6771step0 raw6771; decide +kernel
      have hl : raw6771step0Labels = raw6771Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6771 raw6771Labels permutation346 hz
    mixedMoment B raw6771step0 raw6771step0Labels = mixedMoment B raw6771step1 raw6771step1Labels := by
      have ha : raw6771step1 = (fun i j => raw6771step0 (permutation103 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6771step1 raw6771step0; decide +kernel
      have hl : raw6771step1Labels = raw6771step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6771step0 raw6771step0Labels permutation103 permutation5
    mixedMoment B raw6771step1 raw6771step1Labels = mixedMoment B raw6771step2 raw6771step2Labels := by
      have ha : raw6771step2 = raw6771step1 := by apply Matrix.ext; unfold raw6771step2 raw6771step1; decide +kernel
      have hl : raw6771step1Labels = labelEmbedding1 ∘ raw6771step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6771step1 raw6771step1Labels raw6771step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2092 node2092Labels := by rfl

def raw6772 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![0, 0, 0], ![3, -3, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6772Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6772step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![3, -3, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6772step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6772step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw6772step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6772step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw6772step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6772 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6772 raw6772Labels = mixedMoment B node2093 node2093Labels := by
  calc
    mixedMoment B raw6772 raw6772Labels = mixedMoment B raw6772step0 raw6772step0Labels := by
      have hz : ∀ j, raw6772 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6772step0 = (fun i j => raw6772 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6772step0 raw6772; decide +kernel
      have hl : raw6772step0Labels = raw6772Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6772 raw6772Labels permutation346 hz
    mixedMoment B raw6772step0 raw6772step0Labels = mixedMoment B raw6772step1 raw6772step1Labels := by
      have ha : raw6772step1 = (fun i j => raw6772step0 (permutation102 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6772step1 raw6772step0; decide +kernel
      have hl : raw6772step1Labels = raw6772step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6772step0 raw6772step0Labels permutation102 permutation5
    mixedMoment B raw6772step1 raw6772step1Labels = mixedMoment B raw6772step2 raw6772step2Labels := by
      have ha : raw6772step2 = raw6772step1 := by apply Matrix.ext; unfold raw6772step2 raw6772step1; decide +kernel
      have hl : raw6772step1Labels = labelEmbedding1 ∘ raw6772step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6772step1 raw6772step1Labels raw6772step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2093 node2093Labels := by rfl

def raw6773 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 1, 0], ![3, -3, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6773Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6773step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw6773step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6773step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw6773step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6773 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6773 raw6773Labels = mixedMoment B node2091 node2091Labels := by
  calc
    mixedMoment B raw6773 raw6773Labels = mixedMoment B raw6773step0 raw6773step0Labels := by
      have ha : raw6773step0 = (fun i j => raw6773 (permutation517 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6773step0 raw6773; decide +kernel
      have hl : raw6773step0Labels = raw6773Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6773 raw6773Labels permutation517 permutation5
    mixedMoment B raw6773step0 raw6773step0Labels = mixedMoment B raw6773step1 raw6773step1Labels := by
      have ha : raw6773step1 = raw6773step0 := by apply Matrix.ext; unfold raw6773step1 raw6773step0; decide +kernel
      have hl : raw6773step0Labels = labelEmbedding1 ∘ raw6773step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6773step0 raw6773step0Labels raw6773step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2091 node2091Labels := by rfl

def raw6774 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![3, -3, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw6774Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6774step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![3, -3, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw6774step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6774step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw6774step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6774step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw6774step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6774 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6774 raw6774Labels = mixedMoment B node2111 node2111Labels := by
  calc
    mixedMoment B raw6774 raw6774Labels = mixedMoment B raw6774step0 raw6774step0Labels := by
      have hz : ∀ j, raw6774 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6774step0 = (fun i j => raw6774 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6774step0 raw6774; decide +kernel
      have hl : raw6774step0Labels = raw6774Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6774 raw6774Labels permutation346 hz
    mixedMoment B raw6774step0 raw6774step0Labels = mixedMoment B raw6774step1 raw6774step1Labels := by
      have ha : raw6774step1 = (fun i j => raw6774step0 (permutation101 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6774step1 raw6774step0; decide +kernel
      have hl : raw6774step1Labels = raw6774step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6774step0 raw6774step0Labels permutation101 permutation5
    mixedMoment B raw6774step1 raw6774step1Labels = mixedMoment B raw6774step2 raw6774step2Labels := by
      have ha : raw6774step2 = raw6774step1 := by apply Matrix.ext; unfold raw6774step2 raw6774step1; decide +kernel
      have hl : raw6774step1Labels = labelEmbedding1 ∘ raw6774step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6774step1 raw6774step1Labels raw6774step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2111 node2111Labels := by rfl

def raw6775 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![3, -3, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw6775Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6775step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![3, -3, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw6775step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6775step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw6775step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6775step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw6775step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6775 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6775 raw6775Labels = mixedMoment B node2254 node2254Labels := by
  calc
    mixedMoment B raw6775 raw6775Labels = mixedMoment B raw6775step0 raw6775step0Labels := by
      have hz : ∀ j, raw6775 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6775step0 = (fun i j => raw6775 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6775step0 raw6775; decide +kernel
      have hl : raw6775step0Labels = raw6775Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6775 raw6775Labels permutation346 hz
    mixedMoment B raw6775step0 raw6775step0Labels = mixedMoment B raw6775step1 raw6775step1Labels := by
      have ha : raw6775step1 = (fun i j => raw6775step0 (permutation97 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6775step1 raw6775step0; decide +kernel
      have hl : raw6775step1Labels = raw6775step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6775step0 raw6775step0Labels permutation97 permutation5
    mixedMoment B raw6775step1 raw6775step1Labels = mixedMoment B raw6775step2 raw6775step2Labels := by
      have ha : raw6775step2 = raw6775step1 := by apply Matrix.ext; unfold raw6775step2 raw6775step1; decide +kernel
      have hl : raw6775step1Labels = labelEmbedding1 ∘ raw6775step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6775step1 raw6775step1Labels raw6775step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2254 node2254Labels := by rfl

def raw6776 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw6776Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6776step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![2, -2, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw6776step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6776step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![1, 0, -1], ![-1, 2, -1], ![-1, 1, 0], ![-2, 0, 2]]
def raw6776step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6776step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw6776step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6776step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw6776step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6776 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6776 raw6776Labels = mixedMoment B node3210 node3210Labels := by
  calc
    mixedMoment B raw6776 raw6776Labels = mixedMoment B raw6776step0 raw6776step0Labels := by
      have hz : ∀ j, raw6776 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6776step0 = (fun i j => raw6776 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6776step0 raw6776; decide +kernel
      have hl : raw6776step0Labels = raw6776Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6776 raw6776Labels permutation346 hz
    mixedMoment B raw6776step0 raw6776step0Labels = mixedMoment B raw6776step1 raw6776step1Labels := by
      have ha : raw6776step1 = (fun i j => raw6776step0 (permutation37 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6776step1 raw6776step0; decide +kernel
      have hl : raw6776step1Labels = raw6776step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6776step0 raw6776step0Labels permutation37 permutation5
    mixedMoment B raw6776step1 raw6776step1Labels = mixedMoment B raw6776step2 raw6776step2Labels := by
      have ha : raw6776step2 = -raw6776step1 := by apply Matrix.ext; change ∀ i j, raw6776step2 i j = -(raw6776step1 i j); unfold raw6776step2 raw6776step1; decide +kernel
      have hl : raw6776step2Labels = raw6776step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6776step2 raw6776step2Labels = mixedMoment B raw6776step3 raw6776step3Labels := by
      have ha : raw6776step3 = raw6776step2 := by apply Matrix.ext; unfold raw6776step3 raw6776step2; decide +kernel
      have hl : raw6776step2Labels = labelEmbedding1 ∘ raw6776step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6776step2 raw6776step2Labels raw6776step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3210 node3210Labels := by rfl

def raw6777 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![0, 0, 0], ![2, -2, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw6777Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6777step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![2, -2, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw6777step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6777step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6777step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6777step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6777step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6777 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6777 raw6777Labels = mixedMoment B node3044 node3044Labels := by
  calc
    mixedMoment B raw6777 raw6777Labels = mixedMoment B raw6777step0 raw6777step0Labels := by
      have hz : ∀ j, raw6777 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6777step0 = (fun i j => raw6777 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6777step0 raw6777; decide +kernel
      have hl : raw6777step0Labels = raw6777Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6777 raw6777Labels permutation346 hz
    mixedMoment B raw6777step0 raw6777step0Labels = mixedMoment B raw6777step1 raw6777step1Labels := by
      have ha : raw6777step1 = (fun i j => raw6777step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw6777step1 raw6777step0; decide +kernel
      have hl : raw6777step1Labels = raw6777step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6777step0 raw6777step0Labels permutation38 permutation7
    mixedMoment B raw6777step1 raw6777step1Labels = mixedMoment B raw6777step2 raw6777step2Labels := by
      have ha : raw6777step2 = raw6777step1 := by apply Matrix.ext; unfold raw6777step2 raw6777step1; decide +kernel
      have hl : raw6777step1Labels = labelEmbedding1 ∘ raw6777step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6777step1 raw6777step1Labels raw6777step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3044 node3044Labels := by rfl

def raw6778 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw6778Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6778step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw6778step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6778step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw6778step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6778 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6778 raw6778Labels = mixedMoment B node3029 node3029Labels := by
  calc
    mixedMoment B raw6778 raw6778Labels = mixedMoment B raw6778step0 raw6778step0Labels := by
      have ha : raw6778step0 = (fun i j => raw6778 (permutation200 i) (permutation7 j)) := by apply Matrix.ext; unfold raw6778step0 raw6778; decide +kernel
      have hl : raw6778step0Labels = raw6778Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6778 raw6778Labels permutation200 permutation7
    mixedMoment B raw6778step0 raw6778step0Labels = mixedMoment B raw6778step1 raw6778step1Labels := by
      have ha : raw6778step1 = raw6778step0 := by apply Matrix.ext; unfold raw6778step1 raw6778step0; decide +kernel
      have hl : raw6778step0Labels = labelEmbedding1 ∘ raw6778step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6778step0 raw6778step0Labels raw6778step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3029 node3029Labels := by rfl

def raw6779 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw6779Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6779step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw6779step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6779step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![1, 0, -1], ![0, 1, -1], ![-2, 2, 0], ![-2, 0, 2]]
def raw6779step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6779step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw6779step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6779step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw6779step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6779 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6779 raw6779Labels = mixedMoment B node3206 node3206Labels := by
  calc
    mixedMoment B raw6779 raw6779Labels = mixedMoment B raw6779step0 raw6779step0Labels := by
      have hz : ∀ j, raw6779 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6779step0 = (fun i j => raw6779 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6779step0 raw6779; decide +kernel
      have hl : raw6779step0Labels = raw6779Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6779 raw6779Labels permutation346 hz
    mixedMoment B raw6779step0 raw6779step0Labels = mixedMoment B raw6779step1 raw6779step1Labels := by
      have ha : raw6779step1 = (fun i j => raw6779step0 (permutation35 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6779step1 raw6779step0; decide +kernel
      have hl : raw6779step1Labels = raw6779step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6779step0 raw6779step0Labels permutation35 permutation5
    mixedMoment B raw6779step1 raw6779step1Labels = mixedMoment B raw6779step2 raw6779step2Labels := by
      have ha : raw6779step2 = -raw6779step1 := by apply Matrix.ext; change ∀ i j, raw6779step2 i j = -(raw6779step1 i j); unfold raw6779step2 raw6779step1; decide +kernel
      have hl : raw6779step2Labels = raw6779step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6779step2 raw6779step2Labels = mixedMoment B raw6779step3 raw6779step3Labels := by
      have ha : raw6779step3 = raw6779step2 := by apply Matrix.ext; unfold raw6779step3 raw6779step2; decide +kernel
      have hl : raw6779step2Labels = labelEmbedding1 ∘ raw6779step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6779step2 raw6779step2Labels raw6779step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3206 node3206Labels := by rfl

def raw6780 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw6780Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6780step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![2, -2, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw6780step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6780step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6780step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6780step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6780step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6780 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6780 raw6780Labels = mixedMoment B node3045 node3045Labels := by
  calc
    mixedMoment B raw6780 raw6780Labels = mixedMoment B raw6780step0 raw6780step0Labels := by
      have hz : ∀ j, raw6780 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6780step0 = (fun i j => raw6780 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6780step0 raw6780; decide +kernel
      have hl : raw6780step0Labels = raw6780Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6780 raw6780Labels permutation346 hz
    mixedMoment B raw6780step0 raw6780step0Labels = mixedMoment B raw6780step1 raw6780step1Labels := by
      have ha : raw6780step1 = (fun i j => raw6780step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw6780step1 raw6780step0; decide +kernel
      have hl : raw6780step1Labels = raw6780step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6780step0 raw6780step0Labels permutation38 permutation7
    mixedMoment B raw6780step1 raw6780step1Labels = mixedMoment B raw6780step2 raw6780step2Labels := by
      have ha : raw6780step2 = raw6780step1 := by apply Matrix.ext; unfold raw6780step2 raw6780step1; decide +kernel
      have hl : raw6780step1Labels = labelEmbedding1 ∘ raw6780step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6780step1 raw6780step1Labels raw6780step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3045 node3045Labels := by rfl

def raw6781 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw6781Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6781step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw6781step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6781step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw6781step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6781 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6781 raw6781Labels = mixedMoment B node3030 node3030Labels := by
  calc
    mixedMoment B raw6781 raw6781Labels = mixedMoment B raw6781step0 raw6781step0Labels := by
      have ha : raw6781step0 = (fun i j => raw6781 (permutation200 i) (permutation7 j)) := by apply Matrix.ext; unfold raw6781step0 raw6781; decide +kernel
      have hl : raw6781step0Labels = raw6781Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6781 raw6781Labels permutation200 permutation7
    mixedMoment B raw6781step0 raw6781step0Labels = mixedMoment B raw6781step1 raw6781step1Labels := by
      have ha : raw6781step1 = raw6781step0 := by apply Matrix.ext; unfold raw6781step1 raw6781step0; decide +kernel
      have hl : raw6781step0Labels = labelEmbedding1 ∘ raw6781step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6781step0 raw6781step0Labels raw6781step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3030 node3030Labels := by rfl

def raw6782 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw6782Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6782step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw6782step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6782step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw6782step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6782step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw6782step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6782 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6782 raw6782Labels = mixedMoment B node3089 node3089Labels := by
  calc
    mixedMoment B raw6782 raw6782Labels = mixedMoment B raw6782step0 raw6782step0Labels := by
      have hz : ∀ j, raw6782 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6782step0 = (fun i j => raw6782 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6782step0 raw6782; decide +kernel
      have hl : raw6782step0Labels = raw6782Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6782 raw6782Labels permutation346 hz
    mixedMoment B raw6782step0 raw6782step0Labels = mixedMoment B raw6782step1 raw6782step1Labels := by
      have ha : raw6782step1 = (fun i j => raw6782step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw6782step1 raw6782step0; decide +kernel
      have hl : raw6782step1Labels = raw6782step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6782step0 raw6782step0Labels permutation38 permutation7
    mixedMoment B raw6782step1 raw6782step1Labels = mixedMoment B raw6782step2 raw6782step2Labels := by
      have ha : raw6782step2 = raw6782step1 := by apply Matrix.ext; unfold raw6782step2 raw6782step1; decide +kernel
      have hl : raw6782step1Labels = labelEmbedding1 ∘ raw6782step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6782step1 raw6782step1Labels raw6782step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3089 node3089Labels := by rfl

def raw6783 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw6783Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6783step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw6783step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6783step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6783step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6783step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6783step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6783 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6783 raw6783Labels = mixedMoment B node3040 node3040Labels := by
  calc
    mixedMoment B raw6783 raw6783Labels = mixedMoment B raw6783step0 raw6783step0Labels := by
      have hz : ∀ j, raw6783 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6783step0 = (fun i j => raw6783 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6783step0 raw6783; decide +kernel
      have hl : raw6783step0Labels = raw6783Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6783 raw6783Labels permutation346 hz
    mixedMoment B raw6783step0 raw6783step0Labels = mixedMoment B raw6783step1 raw6783step1Labels := by
      have ha : raw6783step1 = (fun i j => raw6783step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw6783step1 raw6783step0; decide +kernel
      have hl : raw6783step1Labels = raw6783step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6783step0 raw6783step0Labels permutation38 permutation7
    mixedMoment B raw6783step1 raw6783step1Labels = mixedMoment B raw6783step2 raw6783step2Labels := by
      have ha : raw6783step2 = raw6783step1 := by apply Matrix.ext; unfold raw6783step2 raw6783step1; decide +kernel
      have hl : raw6783step1Labels = labelEmbedding1 ∘ raw6783step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6783step1 raw6783step1Labels raw6783step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3040 node3040Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
