import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes51
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes78
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes85

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw9728 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw9728Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9728step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw9728step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9728step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw9728step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9728step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw9728step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9728step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw9728step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9728 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9728 raw9728Labels = mixedMoment B node2264 node2264Labels := by
  calc
    mixedMoment B raw9728 raw9728Labels = mixedMoment B raw9728step0 raw9728step0Labels := by
      have hz : ∀ j, raw9728 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9728step0 = (fun i j => raw9728 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9728step0 raw9728; decide +kernel
      have hl : raw9728step0Labels = raw9728Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9728 raw9728Labels permutation434 hz
    mixedMoment B raw9728step0 raw9728step0Labels = mixedMoment B raw9728step1 raw9728step1Labels := by
      have hz : ∀ j, raw9728step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw9728step1 = (fun i j => raw9728step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw9728step1 raw9728step0; decide +kernel
      have hl : raw9728step1Labels = raw9728step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9728step0 raw9728step0Labels permutation80 hz
    mixedMoment B raw9728step1 raw9728step1Labels = mixedMoment B raw9728step2 raw9728step2Labels := by
      have ha : raw9728step2 = (fun i j => raw9728step1 (permutation10 i) (permutation4 j)) := by apply Matrix.ext; unfold raw9728step2 raw9728step1; decide +kernel
      have hl : raw9728step2Labels = raw9728step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9728step1 raw9728step1Labels permutation10 permutation4
    mixedMoment B raw9728step2 raw9728step2Labels = mixedMoment B raw9728step3 raw9728step3Labels := by
      have ha : raw9728step3 = -raw9728step2 := by apply Matrix.ext; change ∀ i j, raw9728step3 i j = -(raw9728step2 i j); unfold raw9728step3 raw9728step2; decide +kernel
      have hl : raw9728step3Labels = raw9728step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2264 node2264Labels := by rfl

def raw9729 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![1, -3, 2]]
def raw9729Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9729step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![1, -3, 2]]
def raw9729step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9729step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![-2, 1, 1], ![1, -3, 2]]
def raw9729step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9729step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw9729step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9729step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![3, -1, -2]]
def raw9729step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9729 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9729 raw9729Labels = mixedMoment B node2109 node2109Labels := by
  calc
    mixedMoment B raw9729 raw9729Labels = mixedMoment B raw9729step0 raw9729step0Labels := by
      have hz : ∀ j, raw9729 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9729step0 = (fun i j => raw9729 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9729step0 raw9729; decide +kernel
      have hl : raw9729step0Labels = raw9729Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9729 raw9729Labels permutation434 hz
    mixedMoment B raw9729step0 raw9729step0Labels = mixedMoment B raw9729step1 raw9729step1Labels := by
      have hz : ∀ j, raw9729step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw9729step1 = (fun i j => raw9729step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw9729step1 raw9729step0; decide +kernel
      have hl : raw9729step1Labels = raw9729step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9729step0 raw9729step0Labels permutation80 hz
    mixedMoment B raw9729step1 raw9729step1Labels = mixedMoment B raw9729step2 raw9729step2Labels := by
      have ha : raw9729step2 = (fun i j => raw9729step1 (permutation10 i) (permutation4 j)) := by apply Matrix.ext; unfold raw9729step2 raw9729step1; decide +kernel
      have hl : raw9729step2Labels = raw9729step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9729step1 raw9729step1Labels permutation10 permutation4
    mixedMoment B raw9729step2 raw9729step2Labels = mixedMoment B raw9729step3 raw9729step3Labels := by
      have ha : raw9729step3 = -raw9729step2 := by apply Matrix.ext; change ∀ i j, raw9729step3 i j = -(raw9729step2 i j); unfold raw9729step3 raw9729step2; decide +kernel
      have hl : raw9729step3Labels = raw9729step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2109 node2109Labels := by rfl

def raw9730 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9730Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9730step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9730step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9730step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw9730step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw9730step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw9730step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw9730step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw9730step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9730 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9730 raw9730Labels = mixedMoment B node5438 node5438Labels := by
  calc
    mixedMoment B raw9730 raw9730Labels = mixedMoment B raw9730step0 raw9730step0Labels := by
      have hz : ∀ j, raw9730 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9730step0 = (fun i j => raw9730 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9730step0 raw9730; decide +kernel
      have hl : raw9730step0Labels = raw9730Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9730 raw9730Labels permutation346 hz
    mixedMoment B raw9730step0 raw9730step0Labels = mixedMoment B raw9730step1 raw9730step1Labels := by
      have ha : raw9730step1 = (fun i j => raw9730step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9730step1 raw9730step0; decide +kernel
      have hl : raw9730step1Labels = raw9730step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9730step0 raw9730step0Labels permutation38 permutation7
    mixedMoment B raw9730step1 raw9730step1Labels = mixedMoment B raw9730step2 raw9730step2Labels := by
      have ha : raw9730step2 = -raw9730step1 := by apply Matrix.ext; change ∀ i j, raw9730step2 i j = -(raw9730step1 i j); unfold raw9730step2 raw9730step1; decide +kernel
      have hl : raw9730step2Labels = raw9730step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9730step2 raw9730step2Labels = mixedMoment B raw9730step3 raw9730step3Labels := by
      have ha : raw9730step3 = raw9730step2 := by apply Matrix.ext; unfold raw9730step3 raw9730step2; decide +kernel
      have hl : raw9730step2Labels = labelEmbedding10 ∘ raw9730step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9730step2 raw9730step2Labels raw9730step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5438 node5438Labels := by rfl

def raw9731 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9731Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9731step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9731step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9731 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9731 raw9731Labels = mixedMoment B node5424 node5424Labels := by
  calc
    mixedMoment B raw9731 raw9731Labels = mixedMoment B raw9731step0 raw9731step0Labels := by
      have ha : raw9731step0 = (fun i j => raw9731 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9731step0 raw9731; decide +kernel
      have hl : raw9731step0Labels = raw9731Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9731 raw9731Labels permutation182 permutation2
    _ = mixedMoment B node5424 node5424Labels := by rfl

def raw9732 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9732Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9732step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9732step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9732step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9732step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9732 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9732 raw9732Labels = mixedMoment B node5410 node5410Labels := by
  calc
    mixedMoment B raw9732 raw9732Labels = mixedMoment B raw9732step0 raw9732step0Labels := by
      have hz : ∀ j, raw9732 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9732step0 = (fun i j => raw9732 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9732step0 raw9732; decide +kernel
      have hl : raw9732step0Labels = raw9732Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9732 raw9732Labels permutation346 hz
    mixedMoment B raw9732step0 raw9732step0Labels = mixedMoment B raw9732step1 raw9732step1Labels := by
      have ha : raw9732step1 = (fun i j => raw9732step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9732step1 raw9732step0; decide +kernel
      have hl : raw9732step1Labels = raw9732step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9732step0 raw9732step0Labels permutation38 permutation2
    _ = mixedMoment B node5410 node5410Labels := by rfl

def raw9733 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw9733Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9733step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw9733step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9733step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw9733step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw9733step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw9733step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw9733step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw9733step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9733 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9733 raw9733Labels = mixedMoment B node5439 node5439Labels := by
  calc
    mixedMoment B raw9733 raw9733Labels = mixedMoment B raw9733step0 raw9733step0Labels := by
      have hz : ∀ j, raw9733 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9733step0 = (fun i j => raw9733 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9733step0 raw9733; decide +kernel
      have hl : raw9733step0Labels = raw9733Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9733 raw9733Labels permutation346 hz
    mixedMoment B raw9733step0 raw9733step0Labels = mixedMoment B raw9733step1 raw9733step1Labels := by
      have ha : raw9733step1 = (fun i j => raw9733step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9733step1 raw9733step0; decide +kernel
      have hl : raw9733step1Labels = raw9733step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9733step0 raw9733step0Labels permutation38 permutation7
    mixedMoment B raw9733step1 raw9733step1Labels = mixedMoment B raw9733step2 raw9733step2Labels := by
      have ha : raw9733step2 = -raw9733step1 := by apply Matrix.ext; change ∀ i j, raw9733step2 i j = -(raw9733step1 i j); unfold raw9733step2 raw9733step1; decide +kernel
      have hl : raw9733step2Labels = raw9733step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9733step2 raw9733step2Labels = mixedMoment B raw9733step3 raw9733step3Labels := by
      have ha : raw9733step3 = raw9733step2 := by apply Matrix.ext; unfold raw9733step3 raw9733step2; decide +kernel
      have hl : raw9733step2Labels = labelEmbedding10 ∘ raw9733step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9733step2 raw9733step2Labels raw9733step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5439 node5439Labels := by rfl

def raw9734 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw9734Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9734step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw9734step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9734step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw9734step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw9734step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw9734step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw9734step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw9734step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9734 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9734 raw9734Labels = mixedMoment B node5440 node5440Labels := by
  calc
    mixedMoment B raw9734 raw9734Labels = mixedMoment B raw9734step0 raw9734step0Labels := by
      have hz : ∀ j, raw9734 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9734step0 = (fun i j => raw9734 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9734step0 raw9734; decide +kernel
      have hl : raw9734step0Labels = raw9734Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9734 raw9734Labels permutation346 hz
    mixedMoment B raw9734step0 raw9734step0Labels = mixedMoment B raw9734step1 raw9734step1Labels := by
      have ha : raw9734step1 = (fun i j => raw9734step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9734step1 raw9734step0; decide +kernel
      have hl : raw9734step1Labels = raw9734step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9734step0 raw9734step0Labels permutation38 permutation7
    mixedMoment B raw9734step1 raw9734step1Labels = mixedMoment B raw9734step2 raw9734step2Labels := by
      have ha : raw9734step2 = -raw9734step1 := by apply Matrix.ext; change ∀ i j, raw9734step2 i j = -(raw9734step1 i j); unfold raw9734step2 raw9734step1; decide +kernel
      have hl : raw9734step2Labels = raw9734step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9734step2 raw9734step2Labels = mixedMoment B raw9734step3 raw9734step3Labels := by
      have ha : raw9734step3 = raw9734step2 := by apply Matrix.ext; unfold raw9734step3 raw9734step2; decide +kernel
      have hl : raw9734step2Labels = labelEmbedding10 ∘ raw9734step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9734step2 raw9734step2Labels raw9734step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5440 node5440Labels := by rfl

def raw9735 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9735Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9735step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9735step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9735step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9735step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9735 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9735 raw9735Labels = mixedMoment B node4606 node4606Labels := by
  calc
    mixedMoment B raw9735 raw9735Labels = mixedMoment B raw9735step0 raw9735step0Labels := by
      have hz : ∀ j, raw9735 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9735step0 = (fun i j => raw9735 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9735step0 raw9735; decide +kernel
      have hl : raw9735step0Labels = raw9735Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9735 raw9735Labels permutation346 hz
    mixedMoment B raw9735step0 raw9735step0Labels = mixedMoment B raw9735step1 raw9735step1Labels := by
      have ha : raw9735step1 = (fun i j => raw9735step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9735step1 raw9735step0; decide +kernel
      have hl : raw9735step1Labels = raw9735step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9735step0 raw9735step0Labels permutation38 permutation2
    _ = mixedMoment B node4606 node4606Labels := by rfl

def raw9736 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9736Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9736step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9736step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9736 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9736 raw9736Labels = mixedMoment B node5137 node5137Labels := by
  calc
    mixedMoment B raw9736 raw9736Labels = mixedMoment B raw9736step0 raw9736step0Labels := by
      have ha : raw9736step0 = (fun i j => raw9736 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9736step0 raw9736; decide +kernel
      have hl : raw9736step0Labels = raw9736Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9736 raw9736Labels permutation182 permutation2
    _ = mixedMoment B node5137 node5137Labels := by rfl

def raw9737 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9737Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9737step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9737step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9737step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9737step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9737 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9737 raw9737Labels = mixedMoment B node5104 node5104Labels := by
  calc
    mixedMoment B raw9737 raw9737Labels = mixedMoment B raw9737step0 raw9737step0Labels := by
      have hz : ∀ j, raw9737 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9737step0 = (fun i j => raw9737 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9737step0 raw9737; decide +kernel
      have hl : raw9737step0Labels = raw9737Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9737 raw9737Labels permutation346 hz
    mixedMoment B raw9737step0 raw9737step0Labels = mixedMoment B raw9737step1 raw9737step1Labels := by
      have ha : raw9737step1 = (fun i j => raw9737step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9737step1 raw9737step0; decide +kernel
      have hl : raw9737step1Labels = raw9737step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9737step0 raw9737step0Labels permutation38 permutation2
    _ = mixedMoment B node5104 node5104Labels := by rfl

def raw9738 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw9738Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9738step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw9738step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9738step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9738step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9738 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9738 raw9738Labels = mixedMoment B node5259 node5259Labels := by
  calc
    mixedMoment B raw9738 raw9738Labels = mixedMoment B raw9738step0 raw9738step0Labels := by
      have hz : ∀ j, raw9738 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9738step0 = (fun i j => raw9738 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9738step0 raw9738; decide +kernel
      have hl : raw9738step0Labels = raw9738Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9738 raw9738Labels permutation346 hz
    mixedMoment B raw9738step0 raw9738step0Labels = mixedMoment B raw9738step1 raw9738step1Labels := by
      have ha : raw9738step1 = (fun i j => raw9738step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9738step1 raw9738step0; decide +kernel
      have hl : raw9738step1Labels = raw9738step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9738step0 raw9738step0Labels permutation40 permutation2
    _ = mixedMoment B node5259 node5259Labels := by rfl

def raw9739 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw9739Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9739step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw9739step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9739step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw9739step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9739 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9739 raw9739Labels = mixedMoment B node5273 node5273Labels := by
  calc
    mixedMoment B raw9739 raw9739Labels = mixedMoment B raw9739step0 raw9739step0Labels := by
      have hz : ∀ j, raw9739 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9739step0 = (fun i j => raw9739 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9739step0 raw9739; decide +kernel
      have hl : raw9739step0Labels = raw9739Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9739 raw9739Labels permutation346 hz
    mixedMoment B raw9739step0 raw9739step0Labels = mixedMoment B raw9739step1 raw9739step1Labels := by
      have ha : raw9739step1 = (fun i j => raw9739step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9739step1 raw9739step0; decide +kernel
      have hl : raw9739step1Labels = raw9739step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9739step0 raw9739step0Labels permutation38 permutation2
    _ = mixedMoment B node5273 node5273Labels := by rfl

def raw9740 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9740Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9740step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw9740step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9740 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9740 raw9740Labels = mixedMoment B node4590 node4590Labels := by
  calc
    mixedMoment B raw9740 raw9740Labels = mixedMoment B raw9740step0 raw9740step0Labels := by
      have ha : raw9740step0 = (fun i j => raw9740 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9740step0 raw9740; decide +kernel
      have hl : raw9740step0Labels = raw9740Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9740 raw9740Labels permutation200 permutation2
    _ = mixedMoment B node4590 node4590Labels := by rfl

def raw9741 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9741Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9741step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw9741step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9741 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9741 raw9741Labels = mixedMoment B node5185 node5185Labels := by
  calc
    mixedMoment B raw9741 raw9741Labels = mixedMoment B raw9741step0 raw9741step0Labels := by
      have ha : raw9741step0 = (fun i j => raw9741 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9741step0 raw9741; decide +kernel
      have hl : raw9741step0Labels = raw9741Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9741 raw9741Labels permutation158 permutation2
    _ = mixedMoment B node5185 node5185Labels := by rfl

def raw9742 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9742Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9742step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw9742step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9742 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9742 raw9742Labels = mixedMoment B node5073 node5073Labels := by
  calc
    mixedMoment B raw9742 raw9742Labels = mixedMoment B raw9742step0 raw9742step0Labels := by
      have ha : raw9742step0 = (fun i j => raw9742 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9742step0 raw9742; decide +kernel
      have hl : raw9742step0Labels = raw9742Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9742 raw9742Labels permutation200 permutation2
    _ = mixedMoment B node5073 node5073Labels := by rfl

def raw9743 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw9743Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9743step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9743step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9743 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9743 raw9743Labels = mixedMoment B node5250 node5250Labels := by
  calc
    mixedMoment B raw9743 raw9743Labels = mixedMoment B raw9743step0 raw9743step0Labels := by
      have ha : raw9743step0 = (fun i j => raw9743 (permutation202 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9743step0 raw9743; decide +kernel
      have hl : raw9743step0Labels = raw9743Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9743 raw9743Labels permutation202 permutation2
    _ = mixedMoment B node5250 node5250Labels := by rfl

def raw9744 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw9744Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9744step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw9744step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9744 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9744 raw9744Labels = mixedMoment B node5257 node5257Labels := by
  calc
    mixedMoment B raw9744 raw9744Labels = mixedMoment B raw9744step0 raw9744step0Labels := by
      have ha : raw9744step0 = (fun i j => raw9744 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9744step0 raw9744; decide +kernel
      have hl : raw9744step0Labels = raw9744Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9744 raw9744Labels permutation200 permutation2
    _ = mixedMoment B node5257 node5257Labels := by rfl

def raw9745 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9745Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9745step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9745step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9745step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw9745step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9745step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw9745step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9745 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9745 raw9745Labels = mixedMoment B node4603 node4603Labels := by
  calc
    mixedMoment B raw9745 raw9745Labels = mixedMoment B raw9745step0 raw9745step0Labels := by
      have hz : ∀ j, raw9745 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9745step0 = (fun i j => raw9745 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9745step0 raw9745; decide +kernel
      have hl : raw9745step0Labels = raw9745Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9745 raw9745Labels permutation346 hz
    mixedMoment B raw9745step0 raw9745step0Labels = mixedMoment B raw9745step1 raw9745step1Labels := by
      have ha : raw9745step1 = (fun i j => raw9745step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9745step1 raw9745step0; decide +kernel
      have hl : raw9745step1Labels = raw9745step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9745step0 raw9745step0Labels permutation34 permutation3
    mixedMoment B raw9745step1 raw9745step1Labels = mixedMoment B raw9745step2 raw9745step2Labels := by
      have ha : raw9745step2 = raw9745step1 := by apply Matrix.ext; unfold raw9745step2 raw9745step1; decide +kernel
      have hl : raw9745step1Labels = labelEmbedding6 ∘ raw9745step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9745step1 raw9745step1Labels raw9745step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4603 node4603Labels := by rfl

def raw9746 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9746Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9746step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9746step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9746 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9746 raw9746Labels = mixedMoment B node5199 node5199Labels := by
  calc
    mixedMoment B raw9746 raw9746Labels = mixedMoment B raw9746step0 raw9746step0Labels := by
      have hz : ∀ j, raw9746 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9746step0 = (fun i j => raw9746 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9746step0 raw9746; decide +kernel
      have hl : raw9746step0Labels = raw9746Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9746 raw9746Labels permutation346 hz
    _ = mixedMoment B node5199 node5199Labels := by rfl

def raw9747 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9747Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9747step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9747step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9747 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9747 raw9747Labels = mixedMoment B node5145 node5145Labels := by
  calc
    mixedMoment B raw9747 raw9747Labels = mixedMoment B raw9747step0 raw9747step0Labels := by
      have ha : raw9747step0 = (fun i j => raw9747 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9747step0 raw9747; decide +kernel
      have hl : raw9747step0Labels = raw9747Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9747 raw9747Labels permutation176 permutation2
    _ = mixedMoment B node5145 node5145Labels := by rfl

def raw9748 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![0, 1, -1], ![2, -1, -1]]
def raw9748Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9748step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![0, 1, -1], ![2, -1, -1]]
def raw9748step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9748step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw9748step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9748 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9748 raw9748Labels = mixedMoment B node5282 node5282Labels := by
  calc
    mixedMoment B raw9748 raw9748Labels = mixedMoment B raw9748step0 raw9748step0Labels := by
      have hz : ∀ j, raw9748 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9748step0 = (fun i j => raw9748 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9748step0 raw9748; decide +kernel
      have hl : raw9748step0Labels = raw9748Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9748 raw9748Labels permutation346 hz
    mixedMoment B raw9748step0 raw9748step0Labels = mixedMoment B raw9748step1 raw9748step1Labels := by
      have ha : raw9748step1 = (fun i j => raw9748step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9748step1 raw9748step0; decide +kernel
      have hl : raw9748step1Labels = raw9748step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9748step0 raw9748step0Labels permutation34 permutation2
    _ = mixedMoment B node5282 node5282Labels := by rfl

def raw9749 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw9749Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9749step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw9749step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9749 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9749 raw9749Labels = mixedMoment B node5290 node5290Labels := by
  calc
    mixedMoment B raw9749 raw9749Labels = mixedMoment B raw9749step0 raw9749step0Labels := by
      have hz : ∀ j, raw9749 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9749step0 = (fun i j => raw9749 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9749step0 raw9749; decide +kernel
      have hl : raw9749step0Labels = raw9749Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9749 raw9749Labels permutation346 hz
    _ = mixedMoment B node5290 node5290Labels := by rfl

def raw9750 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw9750Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9750step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw9750step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9750step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw9750step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9750 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9750 raw9750Labels = mixedMoment B node4593 node4593Labels := by
  calc
    mixedMoment B raw9750 raw9750Labels = mixedMoment B raw9750step0 raw9750step0Labels := by
      have hz : ∀ j, raw9750 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9750step0 = (fun i j => raw9750 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9750step0 raw9750; decide +kernel
      have hl : raw9750step0Labels = raw9750Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9750 raw9750Labels permutation346 hz
    mixedMoment B raw9750step0 raw9750step0Labels = mixedMoment B raw9750step1 raw9750step1Labels := by
      have ha : raw9750step1 = (fun i j => raw9750step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9750step1 raw9750step0; decide +kernel
      have hl : raw9750step1Labels = raw9750step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9750step0 raw9750step0Labels permutation38 permutation2
    _ = mixedMoment B node4593 node4593Labels := by rfl

def raw9751 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw9751Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9751step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw9751step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9751 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9751 raw9751Labels = mixedMoment B node5189 node5189Labels := by
  calc
    mixedMoment B raw9751 raw9751Labels = mixedMoment B raw9751step0 raw9751step0Labels := by
      have hz : ∀ j, raw9751 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9751step0 = (fun i j => raw9751 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9751step0 raw9751; decide +kernel
      have hl : raw9751step0Labels = raw9751Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9751 raw9751Labels permutation346 hz
    _ = mixedMoment B node5189 node5189Labels := by rfl

def raw9752 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw9752Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9752step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw9752step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9752 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9752 raw9752Labels = mixedMoment B node5130 node5130Labels := by
  calc
    mixedMoment B raw9752 raw9752Labels = mixedMoment B raw9752step0 raw9752step0Labels := by
      have ha : raw9752step0 = (fun i j => raw9752 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9752step0 raw9752; decide +kernel
      have hl : raw9752step0Labels = raw9752Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9752 raw9752Labels permutation182 permutation2
    _ = mixedMoment B node5130 node5130Labels := by rfl

def raw9753 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![2, -1, -1], ![2, -1, -1]]
def raw9753Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9753step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 0, 1], ![2, -1, -1], ![2, -1, -1]]
def raw9753step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9753step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw9753step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9753 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9753 raw9753Labels = mixedMoment B node5081 node5081Labels := by
  calc
    mixedMoment B raw9753 raw9753Labels = mixedMoment B raw9753step0 raw9753step0Labels := by
      have hz : ∀ j, raw9753 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9753step0 = (fun i j => raw9753 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9753step0 raw9753; decide +kernel
      have hl : raw9753step0Labels = raw9753Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9753 raw9753Labels permutation346 hz
    mixedMoment B raw9753step0 raw9753step0Labels = mixedMoment B raw9753step1 raw9753step1Labels := by
      have ha : raw9753step1 = (fun i j => raw9753step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9753step1 raw9753step0; decide +kernel
      have hl : raw9753step1Labels = raw9753step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9753step0 raw9753step0Labels permutation38 permutation2
    _ = mixedMoment B node5081 node5081Labels := by rfl

def raw9754 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1]]
def raw9754Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9754step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1]]
def raw9754step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9754step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9754step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9754 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9754 raw9754Labels = mixedMoment B node5259 node5259Labels := by
  calc
    mixedMoment B raw9754 raw9754Labels = mixedMoment B raw9754step0 raw9754step0Labels := by
      have hz : ∀ j, raw9754 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9754step0 = (fun i j => raw9754 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9754step0 raw9754; decide +kernel
      have hl : raw9754step0Labels = raw9754Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9754 raw9754Labels permutation346 hz
    mixedMoment B raw9754step0 raw9754step0Labels = mixedMoment B raw9754step1 raw9754step1Labels := by
      have ha : raw9754step1 = (fun i j => raw9754step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9754step1 raw9754step0; decide +kernel
      have hl : raw9754step1Labels = raw9754step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9754step0 raw9754step0Labels permutation39 permutation2
    _ = mixedMoment B node5259 node5259Labels := by rfl

def raw9755 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw9755Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9755step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw9755step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9755step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw9755step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9755step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw9755step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9755 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9755 raw9755Labels = mixedMoment B node4591 node4591Labels := by
  calc
    mixedMoment B raw9755 raw9755Labels = mixedMoment B raw9755step0 raw9755step0Labels := by
      have hz : ∀ j, raw9755 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9755step0 = (fun i j => raw9755 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9755step0 raw9755; decide +kernel
      have hl : raw9755step0Labels = raw9755Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9755 raw9755Labels permutation346 hz
    mixedMoment B raw9755step0 raw9755step0Labels = mixedMoment B raw9755step1 raw9755step1Labels := by
      have ha : raw9755step1 = (fun i j => raw9755step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9755step1 raw9755step0; decide +kernel
      have hl : raw9755step1Labels = raw9755step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9755step0 raw9755step0Labels permutation32 permutation3
    mixedMoment B raw9755step1 raw9755step1Labels = mixedMoment B raw9755step2 raw9755step2Labels := by
      have ha : raw9755step2 = raw9755step1 := by apply Matrix.ext; unfold raw9755step2 raw9755step1; decide +kernel
      have hl : raw9755step1Labels = labelEmbedding6 ∘ raw9755step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9755step1 raw9755step1Labels raw9755step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4591 node4591Labels := by rfl

def raw9756 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw9756Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9756step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw9756step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9756step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-3, 2, 1]]
def raw9756step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9756step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw9756step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9756step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw9756step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9756 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9756 raw9756Labels = mixedMoment B node5139 node5139Labels := by
  calc
    mixedMoment B raw9756 raw9756Labels = mixedMoment B raw9756step0 raw9756step0Labels := by
      have hz : ∀ j, raw9756 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9756step0 = (fun i j => raw9756 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9756step0 raw9756; decide +kernel
      have hl : raw9756step0Labels = raw9756Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9756 raw9756Labels permutation346 hz
    mixedMoment B raw9756step0 raw9756step0Labels = mixedMoment B raw9756step1 raw9756step1Labels := by
      have ha : raw9756step1 = (fun i j => raw9756step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9756step1 raw9756step0; decide +kernel
      have hl : raw9756step1Labels = raw9756step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9756step0 raw9756step0Labels permutation151 permutation3
    mixedMoment B raw9756step1 raw9756step1Labels = mixedMoment B raw9756step2 raw9756step2Labels := by
      have ha : raw9756step2 = -raw9756step1 := by apply Matrix.ext; change ∀ i j, raw9756step2 i j = -(raw9756step1 i j); unfold raw9756step2 raw9756step1; decide +kernel
      have hl : raw9756step2Labels = raw9756step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9756step2 raw9756step2Labels = mixedMoment B raw9756step3 raw9756step3Labels := by
      have ha : raw9756step3 = raw9756step2 := by apply Matrix.ext; unfold raw9756step3 raw9756step2; decide +kernel
      have hl : raw9756step2Labels = labelEmbedding6 ∘ raw9756step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9756step2 raw9756step2Labels raw9756step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5139 node5139Labels := by rfl

def raw9757 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw9757Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9757step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw9757step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9757 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9757 raw9757Labels = mixedMoment B node5128 node5128Labels := by
  calc
    mixedMoment B raw9757 raw9757Labels = mixedMoment B raw9757step0 raw9757step0Labels := by
      have ha : raw9757step0 = (fun i j => raw9757 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9757step0 raw9757; decide +kernel
      have hl : raw9757step0Labels = raw9757Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9757 raw9757Labels permutation182 permutation2
    _ = mixedMoment B node5128 node5128Labels := by rfl

def raw9758 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -2, -1]]
def raw9758Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9758step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 0, 1], ![1, 0, -1], ![3, -2, -1]]
def raw9758step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9758step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw9758step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9758 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9758 raw9758Labels = mixedMoment B node5078 node5078Labels := by
  calc
    mixedMoment B raw9758 raw9758Labels = mixedMoment B raw9758step0 raw9758step0Labels := by
      have hz : ∀ j, raw9758 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9758step0 = (fun i j => raw9758 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9758step0 raw9758; decide +kernel
      have hl : raw9758step0Labels = raw9758Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9758 raw9758Labels permutation346 hz
    mixedMoment B raw9758step0 raw9758step0Labels = mixedMoment B raw9758step1 raw9758step1Labels := by
      have ha : raw9758step1 = (fun i j => raw9758step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9758step1 raw9758step0; decide +kernel
      have hl : raw9758step1Labels = raw9758step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9758step0 raw9758step0Labels permutation38 permutation2
    _ = mixedMoment B node5078 node5078Labels := by rfl

def raw9759 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![3, -2, -1]]
def raw9759Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9759step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![0, 1, -1], ![3, -2, -1]]
def raw9759step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9759step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw9759step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9759 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9759 raw9759Labels = mixedMoment B node5252 node5252Labels := by
  calc
    mixedMoment B raw9759 raw9759Labels = mixedMoment B raw9759step0 raw9759step0Labels := by
      have hz : ∀ j, raw9759 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9759step0 = (fun i j => raw9759 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9759step0 raw9759; decide +kernel
      have hl : raw9759step0Labels = raw9759Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9759 raw9759Labels permutation346 hz
    mixedMoment B raw9759step0 raw9759step0Labels = mixedMoment B raw9759step1 raw9759step1Labels := by
      have ha : raw9759step1 = (fun i j => raw9759step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9759step1 raw9759step0; decide +kernel
      have hl : raw9759step1Labels = raw9759step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9759step0 raw9759step0Labels permutation38 permutation2
    _ = mixedMoment B node5252 node5252Labels := by rfl

def raw9760 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9760Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9760step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9760step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9760step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-2, 2, 0]]
def raw9760step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9760step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw9760step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9760 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9760 raw9760Labels = mixedMoment B node3993 node3993Labels := by
  calc
    mixedMoment B raw9760 raw9760Labels = mixedMoment B raw9760step0 raw9760step0Labels := by
      have hz : ∀ j, raw9760 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9760step0 = (fun i j => raw9760 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9760step0 raw9760; decide +kernel
      have hl : raw9760step0Labels = raw9760Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9760 raw9760Labels permutation346 hz
    mixedMoment B raw9760step0 raw9760step0Labels = mixedMoment B raw9760step1 raw9760step1Labels := by
      have ha : raw9760step1 = (fun i j => raw9760step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9760step1 raw9760step0; decide +kernel
      have hl : raw9760step1Labels = raw9760step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9760step0 raw9760step0Labels permutation151 permutation3
    mixedMoment B raw9760step1 raw9760step1Labels = mixedMoment B raw9760step2 raw9760step2Labels := by
      have ha : raw9760step2 = -raw9760step1 := by apply Matrix.ext; change ∀ i j, raw9760step2 i j = -(raw9760step1 i j); unfold raw9760step2 raw9760step1; decide +kernel
      have hl : raw9760step2Labels = raw9760step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3993 node3993Labels := by rfl

def raw9761 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9761Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9761step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw9761step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9761step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw9761step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9761 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9761 raw9761Labels = mixedMoment B node3990 node3990Labels := by
  calc
    mixedMoment B raw9761 raw9761Labels = mixedMoment B raw9761step0 raw9761step0Labels := by
      have ha : raw9761step0 = (fun i j => raw9761 (permutation686 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9761step0 raw9761; decide +kernel
      have hl : raw9761step0Labels = raw9761Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9761 raw9761Labels permutation686 permutation3
    mixedMoment B raw9761step0 raw9761step0Labels = mixedMoment B raw9761step1 raw9761step1Labels := by
      have ha : raw9761step1 = -raw9761step0 := by apply Matrix.ext; change ∀ i j, raw9761step1 i j = -(raw9761step0 i j); unfold raw9761step1 raw9761step0; decide +kernel
      have hl : raw9761step1Labels = raw9761step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3990 node3990Labels := by rfl

def raw9762 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9762Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9762step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9762step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9762step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 2, 0]]
def raw9762step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9762step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw9762step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9762 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9762 raw9762Labels = mixedMoment B node3996 node3996Labels := by
  calc
    mixedMoment B raw9762 raw9762Labels = mixedMoment B raw9762step0 raw9762step0Labels := by
      have hz : ∀ j, raw9762 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9762step0 = (fun i j => raw9762 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9762step0 raw9762; decide +kernel
      have hl : raw9762step0Labels = raw9762Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9762 raw9762Labels permutation346 hz
    mixedMoment B raw9762step0 raw9762step0Labels = mixedMoment B raw9762step1 raw9762step1Labels := by
      have ha : raw9762step1 = (fun i j => raw9762step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9762step1 raw9762step0; decide +kernel
      have hl : raw9762step1Labels = raw9762step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9762step0 raw9762step0Labels permutation149 permutation3
    mixedMoment B raw9762step1 raw9762step1Labels = mixedMoment B raw9762step2 raw9762step2Labels := by
      have ha : raw9762step2 = -raw9762step1 := by apply Matrix.ext; change ∀ i j, raw9762step2 i j = -(raw9762step1 i j); unfold raw9762step2 raw9762step1; decide +kernel
      have hl : raw9762step2Labels = raw9762step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3996 node3996Labels := by rfl

def raw9763 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw9763Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9763step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw9763step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9763step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0]]
def raw9763step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9763step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw9763step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9763 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9763 raw9763Labels = mixedMoment B node4012 node4012Labels := by
  calc
    mixedMoment B raw9763 raw9763Labels = mixedMoment B raw9763step0 raw9763step0Labels := by
      have hz : ∀ j, raw9763 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9763step0 = (fun i j => raw9763 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9763step0 raw9763; decide +kernel
      have hl : raw9763step0Labels = raw9763Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9763 raw9763Labels permutation346 hz
    mixedMoment B raw9763step0 raw9763step0Labels = mixedMoment B raw9763step1 raw9763step1Labels := by
      have ha : raw9763step1 = (fun i j => raw9763step0 (permutation143 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9763step1 raw9763step0; decide +kernel
      have hl : raw9763step1Labels = raw9763step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9763step0 raw9763step0Labels permutation143 permutation3
    mixedMoment B raw9763step1 raw9763step1Labels = mixedMoment B raw9763step2 raw9763step2Labels := by
      have ha : raw9763step2 = -raw9763step1 := by apply Matrix.ext; change ∀ i j, raw9763step2 i j = -(raw9763step1 i j); unfold raw9763step2 raw9763step1; decide +kernel
      have hl : raw9763step2Labels = raw9763step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4012 node4012Labels := by rfl

def raw9764 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw9764Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9764step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw9764step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9764step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -2, 0], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw9764step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9764step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw9764step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9764 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9764 raw9764Labels = mixedMoment B node4036 node4036Labels := by
  calc
    mixedMoment B raw9764 raw9764Labels = mixedMoment B raw9764step0 raw9764step0Labels := by
      have hz : ∀ j, raw9764 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9764step0 = (fun i j => raw9764 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9764step0 raw9764; decide +kernel
      have hl : raw9764step0Labels = raw9764Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9764 raw9764Labels permutation346 hz
    mixedMoment B raw9764step0 raw9764step0Labels = mixedMoment B raw9764step1 raw9764step1Labels := by
      have ha : raw9764step1 = (fun i j => raw9764step0 (permutation41 i) (permutation6 j)) := by apply Matrix.ext; unfold raw9764step1 raw9764step0; decide +kernel
      have hl : raw9764step1Labels = raw9764step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9764step0 raw9764step0Labels permutation41 permutation6
    mixedMoment B raw9764step1 raw9764step1Labels = mixedMoment B raw9764step2 raw9764step2Labels := by
      have ha : raw9764step2 = -raw9764step1 := by apply Matrix.ext; change ∀ i j, raw9764step2 i j = -(raw9764step1 i j); unfold raw9764step2 raw9764step1; decide +kernel
      have hl : raw9764step2Labels = raw9764step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4036 node4036Labels := by rfl

def raw9765 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9765Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9765step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9765step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9765step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw9765step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9765 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9765 raw9765Labels = mixedMoment B node1266 node1266Labels := by
  calc
    mixedMoment B raw9765 raw9765Labels = mixedMoment B raw9765step0 raw9765step0Labels := by
      have hz : ∀ j, raw9765 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9765step0 = (fun i j => raw9765 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9765step0 raw9765; decide +kernel
      have hl : raw9765step0Labels = raw9765Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9765 raw9765Labels permutation346 hz
    mixedMoment B raw9765step0 raw9765step0Labels = mixedMoment B raw9765step1 raw9765step1Labels := by
      have ha : raw9765step1 = (fun i j => raw9765step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9765step1 raw9765step0; decide +kernel
      have hl : raw9765step1Labels = raw9765step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9765step0 raw9765step0Labels permutation38 permutation3
    _ = mixedMoment B node1266 node1266Labels := by rfl

def raw9766 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9766Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9766step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw9766step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9766 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9766 raw9766Labels = mixedMoment B node2936 node2936Labels := by
  calc
    mixedMoment B raw9766 raw9766Labels = mixedMoment B raw9766step0 raw9766step0Labels := by
      have ha : raw9766step0 = (fun i j => raw9766 (permutation182 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9766step0 raw9766; decide +kernel
      have hl : raw9766step0Labels = raw9766Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9766 raw9766Labels permutation182 permutation3
    _ = mixedMoment B node2936 node2936Labels := by rfl

def raw9767 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9767Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9767step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9767step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9767step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw9767step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9767 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9767 raw9767Labels = mixedMoment B node3000 node3000Labels := by
  calc
    mixedMoment B raw9767 raw9767Labels = mixedMoment B raw9767step0 raw9767step0Labels := by
      have hz : ∀ j, raw9767 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9767step0 = (fun i j => raw9767 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9767step0 raw9767; decide +kernel
      have hl : raw9767step0Labels = raw9767Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9767 raw9767Labels permutation346 hz
    mixedMoment B raw9767step0 raw9767step0Labels = mixedMoment B raw9767step1 raw9767step1Labels := by
      have ha : raw9767step1 = (fun i j => raw9767step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9767step1 raw9767step0; decide +kernel
      have hl : raw9767step1Labels = raw9767step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9767step0 raw9767step0Labels permutation38 permutation3
    _ = mixedMoment B node3000 node3000Labels := by rfl

def raw9768 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw9768Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9768step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw9768step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9768step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9768step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9768 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9768 raw9768Labels = mixedMoment B node3088 node3088Labels := by
  calc
    mixedMoment B raw9768 raw9768Labels = mixedMoment B raw9768step0 raw9768step0Labels := by
      have hz : ∀ j, raw9768 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9768step0 = (fun i j => raw9768 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9768step0 raw9768; decide +kernel
      have hl : raw9768step0Labels = raw9768Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9768 raw9768Labels permutation346 hz
    mixedMoment B raw9768step0 raw9768step0Labels = mixedMoment B raw9768step1 raw9768step1Labels := by
      have ha : raw9768step1 = (fun i j => raw9768step0 (permutation46 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9768step1 raw9768step0; decide +kernel
      have hl : raw9768step1Labels = raw9768step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9768step0 raw9768step0Labels permutation46 permutation3
    _ = mixedMoment B node3088 node3088Labels := by rfl

def raw9769 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw9769Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9769step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw9769step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9769step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw9769step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9769 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9769 raw9769Labels = mixedMoment B node3111 node3111Labels := by
  calc
    mixedMoment B raw9769 raw9769Labels = mixedMoment B raw9769step0 raw9769step0Labels := by
      have hz : ∀ j, raw9769 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9769step0 = (fun i j => raw9769 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9769step0 raw9769; decide +kernel
      have hl : raw9769step0Labels = raw9769Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9769 raw9769Labels permutation346 hz
    mixedMoment B raw9769step0 raw9769step0Labels = mixedMoment B raw9769step1 raw9769step1Labels := by
      have ha : raw9769step1 = (fun i j => raw9769step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9769step1 raw9769step0; decide +kernel
      have hl : raw9769step1Labels = raw9769step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9769step0 raw9769step0Labels permutation38 permutation3
    _ = mixedMoment B node3111 node3111Labels := by rfl

def raw9770 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9770Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9770step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw9770step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9770 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9770 raw9770Labels = mixedMoment B node1213 node1213Labels := by
  calc
    mixedMoment B raw9770 raw9770Labels = mixedMoment B raw9770step0 raw9770step0Labels := by
      have ha : raw9770step0 = (fun i j => raw9770 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9770step0 raw9770; decide +kernel
      have hl : raw9770step0Labels = raw9770Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9770 raw9770Labels permutation160 permutation3
    _ = mixedMoment B node1213 node1213Labels := by rfl

def raw9771 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9771Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9771step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw9771step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9771 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9771 raw9771Labels = mixedMoment B node2862 node2862Labels := by
  calc
    mixedMoment B raw9771 raw9771Labels = mixedMoment B raw9771step0 raw9771step0Labels := by
      have ha : raw9771step0 = (fun i j => raw9771 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9771step0 raw9771; decide +kernel
      have hl : raw9771step0Labels = raw9771Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9771 raw9771Labels permutation160 permutation3
    _ = mixedMoment B node2862 node2862Labels := by rfl

def raw9772 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9772Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9772step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw9772step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9772 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9772 raw9772Labels = mixedMoment B node2987 node2987Labels := by
  calc
    mixedMoment B raw9772 raw9772Labels = mixedMoment B raw9772step0 raw9772step0Labels := by
      have ha : raw9772step0 = (fun i j => raw9772 (permutation202 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9772step0 raw9772; decide +kernel
      have hl : raw9772step0Labels = raw9772Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9772 raw9772Labels permutation202 permutation3
    _ = mixedMoment B node2987 node2987Labels := by rfl

def raw9773 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw9773Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9773step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9773step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9773 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9773 raw9773Labels = mixedMoment B node3065 node3065Labels := by
  calc
    mixedMoment B raw9773 raw9773Labels = mixedMoment B raw9773step0 raw9773step0Labels := by
      have ha : raw9773step0 = (fun i j => raw9773 (permutation166 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9773step0 raw9773; decide +kernel
      have hl : raw9773step0Labels = raw9773Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9773 raw9773Labels permutation166 permutation3
    _ = mixedMoment B node3065 node3065Labels := by rfl

def raw9774 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw9774Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9774step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw9774step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9774 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9774 raw9774Labels = mixedMoment B node3087 node3087Labels := by
  calc
    mixedMoment B raw9774 raw9774Labels = mixedMoment B raw9774step0 raw9774step0Labels := by
      have ha : raw9774step0 = (fun i j => raw9774 (permutation161 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9774step0 raw9774; decide +kernel
      have hl : raw9774step0Labels = raw9774Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9774 raw9774Labels permutation161 permutation3
    _ = mixedMoment B node3087 node3087Labels := by rfl

def raw9775 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9775Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9775step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9775step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9775step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw9775step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9775 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9775 raw9775Labels = mixedMoment B node1237 node1237Labels := by
  calc
    mixedMoment B raw9775 raw9775Labels = mixedMoment B raw9775step0 raw9775step0Labels := by
      have hz : ∀ j, raw9775 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9775step0 = (fun i j => raw9775 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9775step0 raw9775; decide +kernel
      have hl : raw9775step0Labels = raw9775Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9775 raw9775Labels permutation346 hz
    mixedMoment B raw9775step0 raw9775step0Labels = mixedMoment B raw9775step1 raw9775step1Labels := by
      have ha : raw9775step1 = (fun i j => raw9775step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9775step1 raw9775step0; decide +kernel
      have hl : raw9775step1Labels = raw9775step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9775step0 raw9775step0Labels permutation34 permutation3
    _ = mixedMoment B node1237 node1237Labels := by rfl

def raw9776 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9776Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9776step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9776step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9776step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw9776step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9776 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9776 raw9776Labels = mixedMoment B node2882 node2882Labels := by
  calc
    mixedMoment B raw9776 raw9776Labels = mixedMoment B raw9776step0 raw9776step0Labels := by
      have hz : ∀ j, raw9776 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9776step0 = (fun i j => raw9776 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9776step0 raw9776; decide +kernel
      have hl : raw9776step0Labels = raw9776Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9776 raw9776Labels permutation346 hz
    mixedMoment B raw9776step0 raw9776step0Labels = mixedMoment B raw9776step1 raw9776step1Labels := by
      have ha : raw9776step1 = (fun i j => raw9776step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9776step1 raw9776step0; decide +kernel
      have hl : raw9776step1Labels = raw9776step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9776step0 raw9776step0Labels permutation34 permutation3
    _ = mixedMoment B node2882 node2882Labels := by rfl

def raw9777 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9777Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9777step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw9777step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9777 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9777 raw9777Labels = mixedMoment B node2925 node2925Labels := by
  calc
    mixedMoment B raw9777 raw9777Labels = mixedMoment B raw9777step0 raw9777step0Labels := by
      have ha : raw9777step0 = (fun i j => raw9777 (permutation178 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9777step0 raw9777; decide +kernel
      have hl : raw9777step0Labels = raw9777Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9777 raw9777Labels permutation178 permutation3
    _ = mixedMoment B node2925 node2925Labels := by rfl

def raw9778 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![0, 1, -1], ![2, -1, -1]]
def raw9778Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9778step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![0, 1, -1], ![2, -1, -1]]
def raw9778step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9778step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw9778step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9778 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9778 raw9778Labels = mixedMoment B node3078 node3078Labels := by
  calc
    mixedMoment B raw9778 raw9778Labels = mixedMoment B raw9778step0 raw9778step0Labels := by
      have hz : ∀ j, raw9778 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9778step0 = (fun i j => raw9778 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9778step0 raw9778; decide +kernel
      have hl : raw9778step0Labels = raw9778Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9778 raw9778Labels permutation346 hz
    mixedMoment B raw9778step0 raw9778step0Labels = mixedMoment B raw9778step1 raw9778step1Labels := by
      have ha : raw9778step1 = (fun i j => raw9778step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9778step1 raw9778step0; decide +kernel
      have hl : raw9778step1Labels = raw9778step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9778step0 raw9778step0Labels permutation34 permutation3
    _ = mixedMoment B node3078 node3078Labels := by rfl

def raw9779 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw9779Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9779step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw9779step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9779step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw9779step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9779 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9779 raw9779Labels = mixedMoment B node3099 node3099Labels := by
  calc
    mixedMoment B raw9779 raw9779Labels = mixedMoment B raw9779step0 raw9779step0Labels := by
      have hz : ∀ j, raw9779 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9779step0 = (fun i j => raw9779 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9779step0 raw9779; decide +kernel
      have hl : raw9779step0Labels = raw9779Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9779 raw9779Labels permutation346 hz
    mixedMoment B raw9779step0 raw9779step0Labels = mixedMoment B raw9779step1 raw9779step1Labels := by
      have ha : raw9779step1 = (fun i j => raw9779step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9779step1 raw9779step0; decide +kernel
      have hl : raw9779step1Labels = raw9779step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9779step0 raw9779step0Labels permutation35 permutation3
    _ = mixedMoment B node3099 node3099Labels := by rfl

def raw9780 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw9780Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9780step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw9780step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9780step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw9780step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9780 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9780 raw9780Labels = mixedMoment B node1220 node1220Labels := by
  calc
    mixedMoment B raw9780 raw9780Labels = mixedMoment B raw9780step0 raw9780step0Labels := by
      have hz : ∀ j, raw9780 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9780step0 = (fun i j => raw9780 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9780step0 raw9780; decide +kernel
      have hl : raw9780step0Labels = raw9780Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9780 raw9780Labels permutation346 hz
    mixedMoment B raw9780step0 raw9780step0Labels = mixedMoment B raw9780step1 raw9780step1Labels := by
      have ha : raw9780step1 = (fun i j => raw9780step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9780step1 raw9780step0; decide +kernel
      have hl : raw9780step1Labels = raw9780step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9780step0 raw9780step0Labels permutation32 permutation3
    _ = mixedMoment B node1220 node1220Labels := by rfl

def raw9781 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw9781Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9781step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw9781step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9781step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw9781step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9781 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9781 raw9781Labels = mixedMoment B node2868 node2868Labels := by
  calc
    mixedMoment B raw9781 raw9781Labels = mixedMoment B raw9781step0 raw9781step0Labels := by
      have hz : ∀ j, raw9781 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9781step0 = (fun i j => raw9781 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9781step0 raw9781; decide +kernel
      have hl : raw9781step0Labels = raw9781Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9781 raw9781Labels permutation346 hz
    mixedMoment B raw9781step0 raw9781step0Labels = mixedMoment B raw9781step1 raw9781step1Labels := by
      have ha : raw9781step1 = (fun i j => raw9781step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9781step1 raw9781step0; decide +kernel
      have hl : raw9781step1Labels = raw9781step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9781step0 raw9781step0Labels permutation32 permutation3
    _ = mixedMoment B node2868 node2868Labels := by rfl

def raw9782 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw9782Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9782step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw9782step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9782 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9782 raw9782Labels = mixedMoment B node2917 node2917Labels := by
  calc
    mixedMoment B raw9782 raw9782Labels = mixedMoment B raw9782step0 raw9782step0Labels := by
      have ha : raw9782step0 = (fun i j => raw9782 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9782step0 raw9782; decide +kernel
      have hl : raw9782step0Labels = raw9782Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9782 raw9782Labels permutation176 permutation3
    _ = mixedMoment B node2917 node2917Labels := by rfl

def raw9783 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![2, -1, -1], ![2, -1, -1]]
def raw9783Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9783step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 0, 1], ![2, -1, -1], ![2, -1, -1]]
def raw9783step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9783step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw9783step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9783 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9783 raw9783Labels = mixedMoment B node2991 node2991Labels := by
  calc
    mixedMoment B raw9783 raw9783Labels = mixedMoment B raw9783step0 raw9783step0Labels := by
      have hz : ∀ j, raw9783 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9783step0 = (fun i j => raw9783 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9783step0 raw9783; decide +kernel
      have hl : raw9783step0Labels = raw9783Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9783 raw9783Labels permutation346 hz
    mixedMoment B raw9783step0 raw9783step0Labels = mixedMoment B raw9783step1 raw9783step1Labels := by
      have ha : raw9783step1 = (fun i j => raw9783step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9783step1 raw9783step0; decide +kernel
      have hl : raw9783step1Labels = raw9783step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9783step0 raw9783step0Labels permutation38 permutation3
    _ = mixedMoment B node2991 node2991Labels := by rfl

def raw9784 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1]]
def raw9784Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9784step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1]]
def raw9784step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9784step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9784step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9784 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9784 raw9784Labels = mixedMoment B node3088 node3088Labels := by
  calc
    mixedMoment B raw9784 raw9784Labels = mixedMoment B raw9784step0 raw9784step0Labels := by
      have hz : ∀ j, raw9784 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9784step0 = (fun i j => raw9784 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9784step0 raw9784; decide +kernel
      have hl : raw9784step0Labels = raw9784Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9784 raw9784Labels permutation346 hz
    mixedMoment B raw9784step0 raw9784step0Labels = mixedMoment B raw9784step1 raw9784step1Labels := by
      have ha : raw9784step1 = (fun i j => raw9784step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9784step1 raw9784step0; decide +kernel
      have hl : raw9784step1Labels = raw9784step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9784step0 raw9784step0Labels permutation33 permutation3
    _ = mixedMoment B node3088 node3088Labels := by rfl

def raw9785 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw9785Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9785step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw9785step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9785step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw9785step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9785 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9785 raw9785Labels = mixedMoment B node1215 node1215Labels := by
  calc
    mixedMoment B raw9785 raw9785Labels = mixedMoment B raw9785step0 raw9785step0Labels := by
      have hz : ∀ j, raw9785 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9785step0 = (fun i j => raw9785 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9785step0 raw9785; decide +kernel
      have hl : raw9785step0Labels = raw9785Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9785 raw9785Labels permutation346 hz
    mixedMoment B raw9785step0 raw9785step0Labels = mixedMoment B raw9785step1 raw9785step1Labels := by
      have ha : raw9785step1 = (fun i j => raw9785step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9785step1 raw9785step0; decide +kernel
      have hl : raw9785step1Labels = raw9785step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9785step0 raw9785step0Labels permutation32 permutation3
    _ = mixedMoment B node1215 node1215Labels := by rfl

def raw9786 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw9786Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9786step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw9786step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9786step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-3, 2, 1]]
def raw9786step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9786step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw9786step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9786 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9786 raw9786Labels = mixedMoment B node2558 node2558Labels := by
  calc
    mixedMoment B raw9786 raw9786Labels = mixedMoment B raw9786step0 raw9786step0Labels := by
      have hz : ∀ j, raw9786 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9786step0 = (fun i j => raw9786 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9786step0 raw9786; decide +kernel
      have hl : raw9786step0Labels = raw9786Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9786 raw9786Labels permutation346 hz
    mixedMoment B raw9786step0 raw9786step0Labels = mixedMoment B raw9786step1 raw9786step1Labels := by
      have ha : raw9786step1 = (fun i j => raw9786step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9786step1 raw9786step0; decide +kernel
      have hl : raw9786step1Labels = raw9786step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9786step0 raw9786step0Labels permutation151 permutation3
    mixedMoment B raw9786step1 raw9786step1Labels = mixedMoment B raw9786step2 raw9786step2Labels := by
      have ha : raw9786step2 = -raw9786step1 := by apply Matrix.ext; change ∀ i j, raw9786step2 i j = -(raw9786step1 i j); unfold raw9786step2 raw9786step1; decide +kernel
      have hl : raw9786step2Labels = raw9786step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2558 node2558Labels := by rfl

def raw9787 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw9787Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9787step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw9787step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9787step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw9787step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9787 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9787 raw9787Labels = mixedMoment B node2543 node2543Labels := by
  calc
    mixedMoment B raw9787 raw9787Labels = mixedMoment B raw9787step0 raw9787step0Labels := by
      have ha : raw9787step0 = (fun i j => raw9787 (permutation686 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9787step0 raw9787; decide +kernel
      have hl : raw9787step0Labels = raw9787Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9787 raw9787Labels permutation686 permutation3
    mixedMoment B raw9787step0 raw9787step0Labels = mixedMoment B raw9787step1 raw9787step1Labels := by
      have ha : raw9787step1 = -raw9787step0 := by apply Matrix.ext; change ∀ i j, raw9787step1 i j = -(raw9787step0 i j); unfold raw9787step1 raw9787step0; decide +kernel
      have hl : raw9787step1Labels = raw9787step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2543 node2543Labels := by rfl

def raw9788 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -2, -1]]
def raw9788Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9788step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 0, 1], ![1, 0, -1], ![3, -2, -1]]
def raw9788step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9788step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-3, 2, 1]]
def raw9788step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9788step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw9788step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9788 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9788 raw9788Labels = mixedMoment B node2572 node2572Labels := by
  calc
    mixedMoment B raw9788 raw9788Labels = mixedMoment B raw9788step0 raw9788step0Labels := by
      have hz : ∀ j, raw9788 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9788step0 = (fun i j => raw9788 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9788step0 raw9788; decide +kernel
      have hl : raw9788step0Labels = raw9788Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9788 raw9788Labels permutation346 hz
    mixedMoment B raw9788step0 raw9788step0Labels = mixedMoment B raw9788step1 raw9788step1Labels := by
      have ha : raw9788step1 = (fun i j => raw9788step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9788step1 raw9788step0; decide +kernel
      have hl : raw9788step1Labels = raw9788step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9788step0 raw9788step0Labels permutation149 permutation3
    mixedMoment B raw9788step1 raw9788step1Labels = mixedMoment B raw9788step2 raw9788step2Labels := by
      have ha : raw9788step2 = -raw9788step1 := by apply Matrix.ext; change ∀ i j, raw9788step2 i j = -(raw9788step1 i j); unfold raw9788step2 raw9788step1; decide +kernel
      have hl : raw9788step2Labels = raw9788step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2572 node2572Labels := by rfl

def raw9789 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![3, -2, -1]]
def raw9789Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9789step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![0, 1, -1], ![3, -2, -1]]
def raw9789step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9789step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw9789step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9789step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw9789step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9789 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9789 raw9789Labels = mixedMoment B node2712 node2712Labels := by
  calc
    mixedMoment B raw9789 raw9789Labels = mixedMoment B raw9789step0 raw9789step0Labels := by
      have hz : ∀ j, raw9789 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9789step0 = (fun i j => raw9789 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9789step0 raw9789; decide +kernel
      have hl : raw9789step0Labels = raw9789Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9789 raw9789Labels permutation346 hz
    mixedMoment B raw9789step0 raw9789step0Labels = mixedMoment B raw9789step1 raw9789step1Labels := by
      have ha : raw9789step1 = (fun i j => raw9789step0 (permutation143 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9789step1 raw9789step0; decide +kernel
      have hl : raw9789step1Labels = raw9789step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9789step0 raw9789step0Labels permutation143 permutation3
    mixedMoment B raw9789step1 raw9789step1Labels = mixedMoment B raw9789step2 raw9789step2Labels := by
      have ha : raw9789step2 = -raw9789step1 := by apply Matrix.ext; change ∀ i j, raw9789step2 i j = -(raw9789step1 i j); unfold raw9789step2 raw9789step1; decide +kernel
      have hl : raw9789step2Labels = raw9789step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2712 node2712Labels := by rfl

def raw9790 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9790Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9790step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9790step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9790step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw9790step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9790step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw9790step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9790step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw9790step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9790 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9790 raw9790Labels = mixedMoment B node3857 node3857Labels := by
  calc
    mixedMoment B raw9790 raw9790Labels = mixedMoment B raw9790step0 raw9790step0Labels := by
      have hz : ∀ j, raw9790 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9790step0 = (fun i j => raw9790 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9790step0 raw9790; decide +kernel
      have hl : raw9790step0Labels = raw9790Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9790 raw9790Labels permutation346 hz
    mixedMoment B raw9790step0 raw9790step0Labels = mixedMoment B raw9790step1 raw9790step1Labels := by
      have ha : raw9790step1 = (fun i j => raw9790step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9790step1 raw9790step0; decide +kernel
      have hl : raw9790step1Labels = raw9790step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9790step0 raw9790step0Labels permutation38 permutation7
    mixedMoment B raw9790step1 raw9790step1Labels = mixedMoment B raw9790step2 raw9790step2Labels := by
      have ha : raw9790step2 = -raw9790step1 := by apply Matrix.ext; change ∀ i j, raw9790step2 i j = -(raw9790step1 i j); unfold raw9790step2 raw9790step1; decide +kernel
      have hl : raw9790step2Labels = raw9790step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9790step2 raw9790step2Labels = mixedMoment B raw9790step3 raw9790step3Labels := by
      have ha : raw9790step3 = raw9790step2 := by apply Matrix.ext; unfold raw9790step3 raw9790step2; decide +kernel
      have hl : raw9790step2Labels = labelEmbedding1 ∘ raw9790step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9790step2 raw9790step2Labels raw9790step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3857 node3857Labels := by rfl

def raw9791 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9791Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9791step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw9791step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9791step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw9791step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9791step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw9791step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9791 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9791 raw9791Labels = mixedMoment B node3843 node3843Labels := by
  calc
    mixedMoment B raw9791 raw9791Labels = mixedMoment B raw9791step0 raw9791step0Labels := by
      have ha : raw9791step0 = (fun i j => raw9791 (permutation206 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9791step0 raw9791; decide +kernel
      have hl : raw9791step0Labels = raw9791Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9791 raw9791Labels permutation206 permutation7
    mixedMoment B raw9791step0 raw9791step0Labels = mixedMoment B raw9791step1 raw9791step1Labels := by
      have ha : raw9791step1 = -raw9791step0 := by apply Matrix.ext; change ∀ i j, raw9791step1 i j = -(raw9791step0 i j); unfold raw9791step1 raw9791step0; decide +kernel
      have hl : raw9791step1Labels = raw9791step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9791step1 raw9791step1Labels = mixedMoment B raw9791step2 raw9791step2Labels := by
      have ha : raw9791step2 = raw9791step1 := by apply Matrix.ext; unfold raw9791step2 raw9791step1; decide +kernel
      have hl : raw9791step1Labels = labelEmbedding1 ∘ raw9791step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9791step1 raw9791step1Labels raw9791step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3843 node3843Labels := by rfl

def raw9792 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9792Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9792step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9792step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9792step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw9792step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9792step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw9792step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9792step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw9792step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9792 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9792 raw9792Labels = mixedMoment B node3816 node3816Labels := by
  calc
    mixedMoment B raw9792 raw9792Labels = mixedMoment B raw9792step0 raw9792step0Labels := by
      have hz : ∀ j, raw9792 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9792step0 = (fun i j => raw9792 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9792step0 raw9792; decide +kernel
      have hl : raw9792step0Labels = raw9792Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9792 raw9792Labels permutation346 hz
    mixedMoment B raw9792step0 raw9792step0Labels = mixedMoment B raw9792step1 raw9792step1Labels := by
      have ha : raw9792step1 = (fun i j => raw9792step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9792step1 raw9792step0; decide +kernel
      have hl : raw9792step1Labels = raw9792step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9792step0 raw9792step0Labels permutation38 permutation7
    mixedMoment B raw9792step1 raw9792step1Labels = mixedMoment B raw9792step2 raw9792step2Labels := by
      have ha : raw9792step2 = -raw9792step1 := by apply Matrix.ext; change ∀ i j, raw9792step2 i j = -(raw9792step1 i j); unfold raw9792step2 raw9792step1; decide +kernel
      have hl : raw9792step2Labels = raw9792step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9792step2 raw9792step2Labels = mixedMoment B raw9792step3 raw9792step3Labels := by
      have ha : raw9792step3 = raw9792step2 := by apply Matrix.ext; unfold raw9792step3 raw9792step2; decide +kernel
      have hl : raw9792step2Labels = labelEmbedding1 ∘ raw9792step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9792step2 raw9792step2Labels raw9792step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3816 node3816Labels := by rfl

def raw9793 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw9793Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9793step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw9793step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9793step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw9793step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9793step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw9793step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9793step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw9793step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9793 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9793 raw9793Labels = mixedMoment B node3858 node3858Labels := by
  calc
    mixedMoment B raw9793 raw9793Labels = mixedMoment B raw9793step0 raw9793step0Labels := by
      have hz : ∀ j, raw9793 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9793step0 = (fun i j => raw9793 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9793step0 raw9793; decide +kernel
      have hl : raw9793step0Labels = raw9793Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9793 raw9793Labels permutation346 hz
    mixedMoment B raw9793step0 raw9793step0Labels = mixedMoment B raw9793step1 raw9793step1Labels := by
      have ha : raw9793step1 = (fun i j => raw9793step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9793step1 raw9793step0; decide +kernel
      have hl : raw9793step1Labels = raw9793step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9793step0 raw9793step0Labels permutation38 permutation7
    mixedMoment B raw9793step1 raw9793step1Labels = mixedMoment B raw9793step2 raw9793step2Labels := by
      have ha : raw9793step2 = -raw9793step1 := by apply Matrix.ext; change ∀ i j, raw9793step2 i j = -(raw9793step1 i j); unfold raw9793step2 raw9793step1; decide +kernel
      have hl : raw9793step2Labels = raw9793step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9793step2 raw9793step2Labels = mixedMoment B raw9793step3 raw9793step3Labels := by
      have ha : raw9793step3 = raw9793step2 := by apply Matrix.ext; unfold raw9793step3 raw9793step2; decide +kernel
      have hl : raw9793step2Labels = labelEmbedding1 ∘ raw9793step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9793step2 raw9793step2Labels raw9793step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3858 node3858Labels := by rfl

def raw9794 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw9794Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9794step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw9794step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9794step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw9794step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9794step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw9794step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9794step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw9794step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9794 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9794 raw9794Labels = mixedMoment B node3859 node3859Labels := by
  calc
    mixedMoment B raw9794 raw9794Labels = mixedMoment B raw9794step0 raw9794step0Labels := by
      have hz : ∀ j, raw9794 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9794step0 = (fun i j => raw9794 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9794step0 raw9794; decide +kernel
      have hl : raw9794step0Labels = raw9794Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9794 raw9794Labels permutation346 hz
    mixedMoment B raw9794step0 raw9794step0Labels = mixedMoment B raw9794step1 raw9794step1Labels := by
      have ha : raw9794step1 = (fun i j => raw9794step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9794step1 raw9794step0; decide +kernel
      have hl : raw9794step1Labels = raw9794step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9794step0 raw9794step0Labels permutation38 permutation7
    mixedMoment B raw9794step1 raw9794step1Labels = mixedMoment B raw9794step2 raw9794step2Labels := by
      have ha : raw9794step2 = -raw9794step1 := by apply Matrix.ext; change ∀ i j, raw9794step2 i j = -(raw9794step1 i j); unfold raw9794step2 raw9794step1; decide +kernel
      have hl : raw9794step2Labels = raw9794step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9794step2 raw9794step2Labels = mixedMoment B raw9794step3 raw9794step3Labels := by
      have ha : raw9794step3 = raw9794step2 := by apply Matrix.ext; unfold raw9794step3 raw9794step2; decide +kernel
      have hl : raw9794step2Labels = labelEmbedding1 ∘ raw9794step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9794step2 raw9794step2Labels raw9794step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3859 node3859Labels := by rfl

def raw9795 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9795Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9795step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9795step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9795step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw9795step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9795step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw9795step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9795step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw9795step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9795 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9795 raw9795Labels = mixedMoment B node3299 node3299Labels := by
  calc
    mixedMoment B raw9795 raw9795Labels = mixedMoment B raw9795step0 raw9795step0Labels := by
      have hz : ∀ j, raw9795 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9795step0 = (fun i j => raw9795 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9795step0 raw9795; decide +kernel
      have hl : raw9795step0Labels = raw9795Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9795 raw9795Labels permutation346 hz
    mixedMoment B raw9795step0 raw9795step0Labels = mixedMoment B raw9795step1 raw9795step1Labels := by
      have ha : raw9795step1 = (fun i j => raw9795step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9795step1 raw9795step0; decide +kernel
      have hl : raw9795step1Labels = raw9795step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9795step0 raw9795step0Labels permutation38 permutation7
    mixedMoment B raw9795step1 raw9795step1Labels = mixedMoment B raw9795step2 raw9795step2Labels := by
      have ha : raw9795step2 = -raw9795step1 := by apply Matrix.ext; change ∀ i j, raw9795step2 i j = -(raw9795step1 i j); unfold raw9795step2 raw9795step1; decide +kernel
      have hl : raw9795step2Labels = raw9795step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9795step2 raw9795step2Labels = mixedMoment B raw9795step3 raw9795step3Labels := by
      have ha : raw9795step3 = raw9795step2 := by apply Matrix.ext; unfold raw9795step3 raw9795step2; decide +kernel
      have hl : raw9795step2Labels = labelEmbedding1 ∘ raw9795step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9795step2 raw9795step2Labels raw9795step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3299 node3299Labels := by rfl

def raw9796 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9796Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9796step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw9796step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9796step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw9796step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9796step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw9796step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9796 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9796 raw9796Labels = mixedMoment B node3521 node3521Labels := by
  calc
    mixedMoment B raw9796 raw9796Labels = mixedMoment B raw9796step0 raw9796step0Labels := by
      have ha : raw9796step0 = (fun i j => raw9796 (permutation206 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9796step0 raw9796; decide +kernel
      have hl : raw9796step0Labels = raw9796Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9796 raw9796Labels permutation206 permutation7
    mixedMoment B raw9796step0 raw9796step0Labels = mixedMoment B raw9796step1 raw9796step1Labels := by
      have ha : raw9796step1 = -raw9796step0 := by apply Matrix.ext; change ∀ i j, raw9796step1 i j = -(raw9796step0 i j); unfold raw9796step1 raw9796step0; decide +kernel
      have hl : raw9796step1Labels = raw9796step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9796step1 raw9796step1Labels = mixedMoment B raw9796step2 raw9796step2Labels := by
      have ha : raw9796step2 = raw9796step1 := by apply Matrix.ext; unfold raw9796step2 raw9796step1; decide +kernel
      have hl : raw9796step1Labels = labelEmbedding1 ∘ raw9796step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9796step1 raw9796step1Labels raw9796step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3521 node3521Labels := by rfl

def raw9797 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9797Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9797step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9797step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9797step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw9797step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9797step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw9797step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9797step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw9797step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9797 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9797 raw9797Labels = mixedMoment B node3483 node3483Labels := by
  calc
    mixedMoment B raw9797 raw9797Labels = mixedMoment B raw9797step0 raw9797step0Labels := by
      have hz : ∀ j, raw9797 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9797step0 = (fun i j => raw9797 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9797step0 raw9797; decide +kernel
      have hl : raw9797step0Labels = raw9797Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9797 raw9797Labels permutation346 hz
    mixedMoment B raw9797step0 raw9797step0Labels = mixedMoment B raw9797step1 raw9797step1Labels := by
      have ha : raw9797step1 = (fun i j => raw9797step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9797step1 raw9797step0; decide +kernel
      have hl : raw9797step1Labels = raw9797step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9797step0 raw9797step0Labels permutation38 permutation7
    mixedMoment B raw9797step1 raw9797step1Labels = mixedMoment B raw9797step2 raw9797step2Labels := by
      have ha : raw9797step2 = -raw9797step1 := by apply Matrix.ext; change ∀ i j, raw9797step2 i j = -(raw9797step1 i j); unfold raw9797step2 raw9797step1; decide +kernel
      have hl : raw9797step2Labels = raw9797step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9797step2 raw9797step2Labels = mixedMoment B raw9797step3 raw9797step3Labels := by
      have ha : raw9797step3 = raw9797step2 := by apply Matrix.ext; unfold raw9797step3 raw9797step2; decide +kernel
      have hl : raw9797step2Labels = labelEmbedding1 ∘ raw9797step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9797step2 raw9797step2Labels raw9797step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3483 node3483Labels := by rfl

def raw9798 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw9798Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9798step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw9798step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9798step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw9798step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9798step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw9798step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9798step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw9798step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9798 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9798 raw9798Labels = mixedMoment B node3544 node3544Labels := by
  calc
    mixedMoment B raw9798 raw9798Labels = mixedMoment B raw9798step0 raw9798step0Labels := by
      have hz : ∀ j, raw9798 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9798step0 = (fun i j => raw9798 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9798step0 raw9798; decide +kernel
      have hl : raw9798step0Labels = raw9798Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9798 raw9798Labels permutation346 hz
    mixedMoment B raw9798step0 raw9798step0Labels = mixedMoment B raw9798step1 raw9798step1Labels := by
      have ha : raw9798step1 = (fun i j => raw9798step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9798step1 raw9798step0; decide +kernel
      have hl : raw9798step1Labels = raw9798step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9798step0 raw9798step0Labels permutation40 permutation7
    mixedMoment B raw9798step1 raw9798step1Labels = mixedMoment B raw9798step2 raw9798step2Labels := by
      have ha : raw9798step2 = -raw9798step1 := by apply Matrix.ext; change ∀ i j, raw9798step2 i j = -(raw9798step1 i j); unfold raw9798step2 raw9798step1; decide +kernel
      have hl : raw9798step2Labels = raw9798step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9798step2 raw9798step2Labels = mixedMoment B raw9798step3 raw9798step3Labels := by
      have ha : raw9798step3 = raw9798step2 := by apply Matrix.ext; unfold raw9798step3 raw9798step2; decide +kernel
      have hl : raw9798step2Labels = labelEmbedding1 ∘ raw9798step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9798step2 raw9798step2Labels raw9798step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3544 node3544Labels := by rfl

def raw9799 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw9799Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9799step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw9799step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9799step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw9799step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9799step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw9799step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9799step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw9799step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9799 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9799 raw9799Labels = mixedMoment B node3546 node3546Labels := by
  calc
    mixedMoment B raw9799 raw9799Labels = mixedMoment B raw9799step0 raw9799step0Labels := by
      have hz : ∀ j, raw9799 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9799step0 = (fun i j => raw9799 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9799step0 raw9799; decide +kernel
      have hl : raw9799step0Labels = raw9799Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9799 raw9799Labels permutation346 hz
    mixedMoment B raw9799step0 raw9799step0Labels = mixedMoment B raw9799step1 raw9799step1Labels := by
      have ha : raw9799step1 = (fun i j => raw9799step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9799step1 raw9799step0; decide +kernel
      have hl : raw9799step1Labels = raw9799step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9799step0 raw9799step0Labels permutation38 permutation7
    mixedMoment B raw9799step1 raw9799step1Labels = mixedMoment B raw9799step2 raw9799step2Labels := by
      have ha : raw9799step2 = -raw9799step1 := by apply Matrix.ext; change ∀ i j, raw9799step2 i j = -(raw9799step1 i j); unfold raw9799step2 raw9799step1; decide +kernel
      have hl : raw9799step2Labels = raw9799step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9799step2 raw9799step2Labels = mixedMoment B raw9799step3 raw9799step3Labels := by
      have ha : raw9799step3 = raw9799step2 := by apply Matrix.ext; unfold raw9799step3 raw9799step2; decide +kernel
      have hl : raw9799step2Labels = labelEmbedding1 ∘ raw9799step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9799step2 raw9799step2Labels raw9799step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3546 node3546Labels := by rfl

def raw9800 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9800Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9800step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw9800step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9800step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw9800step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9800step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw9800step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9800 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9800 raw9800Labels = mixedMoment B node3290 node3290Labels := by
  calc
    mixedMoment B raw9800 raw9800Labels = mixedMoment B raw9800step0 raw9800step0Labels := by
      have ha : raw9800step0 = (fun i j => raw9800 (permutation166 i) (permutation5 j)) := by apply Matrix.ext; unfold raw9800step0 raw9800; decide +kernel
      have hl : raw9800step0Labels = raw9800Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9800 raw9800Labels permutation166 permutation5
    mixedMoment B raw9800step0 raw9800step0Labels = mixedMoment B raw9800step1 raw9800step1Labels := by
      have ha : raw9800step1 = -raw9800step0 := by apply Matrix.ext; change ∀ i j, raw9800step1 i j = -(raw9800step0 i j); unfold raw9800step1 raw9800step0; decide +kernel
      have hl : raw9800step1Labels = raw9800step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9800step1 raw9800step1Labels = mixedMoment B raw9800step2 raw9800step2Labels := by
      have ha : raw9800step2 = raw9800step1 := by apply Matrix.ext; unfold raw9800step2 raw9800step1; decide +kernel
      have hl : raw9800step1Labels = labelEmbedding1 ∘ raw9800step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9800step1 raw9800step1Labels raw9800step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3290 node3290Labels := by rfl

def raw9801 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9801Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9801step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw9801step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9801step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw9801step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9801step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw9801step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9801 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9801 raw9801Labels = mixedMoment B node3529 node3529Labels := by
  calc
    mixedMoment B raw9801 raw9801Labels = mixedMoment B raw9801step0 raw9801step0Labels := by
      have ha : raw9801step0 = (fun i j => raw9801 (permutation206 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9801step0 raw9801; decide +kernel
      have hl : raw9801step0Labels = raw9801Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9801 raw9801Labels permutation206 permutation7
    mixedMoment B raw9801step0 raw9801step0Labels = mixedMoment B raw9801step1 raw9801step1Labels := by
      have ha : raw9801step1 = -raw9801step0 := by apply Matrix.ext; change ∀ i j, raw9801step1 i j = -(raw9801step0 i j); unfold raw9801step1 raw9801step0; decide +kernel
      have hl : raw9801step1Labels = raw9801step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9801step1 raw9801step1Labels = mixedMoment B raw9801step2 raw9801step2Labels := by
      have ha : raw9801step2 = raw9801step1 := by apply Matrix.ext; unfold raw9801step2 raw9801step1; decide +kernel
      have hl : raw9801step1Labels = labelEmbedding1 ∘ raw9801step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9801step1 raw9801step1Labels raw9801step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3529 node3529Labels := by rfl

def raw9802 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9802Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9802step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw9802step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9802step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw9802step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9802step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw9802step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9802 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9802 raw9802Labels = mixedMoment B node3467 node3467Labels := by
  calc
    mixedMoment B raw9802 raw9802Labels = mixedMoment B raw9802step0 raw9802step0Labels := by
      have ha : raw9802step0 = (fun i j => raw9802 (permutation206 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9802step0 raw9802; decide +kernel
      have hl : raw9802step0Labels = raw9802Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9802 raw9802Labels permutation206 permutation7
    mixedMoment B raw9802step0 raw9802step0Labels = mixedMoment B raw9802step1 raw9802step1Labels := by
      have ha : raw9802step1 = -raw9802step0 := by apply Matrix.ext; change ∀ i j, raw9802step1 i j = -(raw9802step0 i j); unfold raw9802step1 raw9802step0; decide +kernel
      have hl : raw9802step1Labels = raw9802step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9802step1 raw9802step1Labels = mixedMoment B raw9802step2 raw9802step2Labels := by
      have ha : raw9802step2 = raw9802step1 := by apply Matrix.ext; unfold raw9802step2 raw9802step1; decide +kernel
      have hl : raw9802step1Labels = labelEmbedding1 ∘ raw9802step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9802step1 raw9802step1Labels raw9802step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3467 node3467Labels := by rfl

def raw9803 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw9803Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9803step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw9803step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9803step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw9803step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9803step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw9803step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9803 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9803 raw9803Labels = mixedMoment B node3531 node3531Labels := by
  calc
    mixedMoment B raw9803 raw9803Labels = mixedMoment B raw9803step0 raw9803step0Labels := by
      have ha : raw9803step0 = (fun i j => raw9803 (permutation206 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9803step0 raw9803; decide +kernel
      have hl : raw9803step0Labels = raw9803Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9803 raw9803Labels permutation206 permutation7
    mixedMoment B raw9803step0 raw9803step0Labels = mixedMoment B raw9803step1 raw9803step1Labels := by
      have ha : raw9803step1 = -raw9803step0 := by apply Matrix.ext; change ∀ i j, raw9803step1 i j = -(raw9803step0 i j); unfold raw9803step1 raw9803step0; decide +kernel
      have hl : raw9803step1Labels = raw9803step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9803step1 raw9803step1Labels = mixedMoment B raw9803step2 raw9803step2Labels := by
      have ha : raw9803step2 = raw9803step1 := by apply Matrix.ext; unfold raw9803step2 raw9803step1; decide +kernel
      have hl : raw9803step1Labels = labelEmbedding1 ∘ raw9803step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9803step1 raw9803step1Labels raw9803step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3531 node3531Labels := by rfl

def raw9804 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw9804Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9804step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw9804step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9804step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw9804step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9804step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw9804step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9804 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9804 raw9804Labels = mixedMoment B node3532 node3532Labels := by
  calc
    mixedMoment B raw9804 raw9804Labels = mixedMoment B raw9804step0 raw9804step0Labels := by
      have ha : raw9804step0 = (fun i j => raw9804 (permutation206 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9804step0 raw9804; decide +kernel
      have hl : raw9804step0Labels = raw9804Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9804 raw9804Labels permutation206 permutation7
    mixedMoment B raw9804step0 raw9804step0Labels = mixedMoment B raw9804step1 raw9804step1Labels := by
      have ha : raw9804step1 = -raw9804step0 := by apply Matrix.ext; change ∀ i j, raw9804step1 i j = -(raw9804step0 i j); unfold raw9804step1 raw9804step0; decide +kernel
      have hl : raw9804step1Labels = raw9804step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9804step1 raw9804step1Labels = mixedMoment B raw9804step2 raw9804step2Labels := by
      have ha : raw9804step2 = raw9804step1 := by apply Matrix.ext; unfold raw9804step2 raw9804step1; decide +kernel
      have hl : raw9804step1Labels = labelEmbedding1 ∘ raw9804step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9804step1 raw9804step1Labels raw9804step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3532 node3532Labels := by rfl

def raw9805 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9805Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9805step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9805step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9805step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw9805step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9805step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw9805step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9805step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw9805step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9805 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9805 raw9805Labels = mixedMoment B node3294 node3294Labels := by
  calc
    mixedMoment B raw9805 raw9805Labels = mixedMoment B raw9805step0 raw9805step0Labels := by
      have hz : ∀ j, raw9805 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9805step0 = (fun i j => raw9805 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9805step0 raw9805; decide +kernel
      have hl : raw9805step0Labels = raw9805Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9805 raw9805Labels permutation346 hz
    mixedMoment B raw9805step0 raw9805step0Labels = mixedMoment B raw9805step1 raw9805step1Labels := by
      have ha : raw9805step1 = (fun i j => raw9805step0 (permutation35 i) (permutation5 j)) := by apply Matrix.ext; unfold raw9805step1 raw9805step0; decide +kernel
      have hl : raw9805step1Labels = raw9805step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9805step0 raw9805step0Labels permutation35 permutation5
    mixedMoment B raw9805step1 raw9805step1Labels = mixedMoment B raw9805step2 raw9805step2Labels := by
      have ha : raw9805step2 = -raw9805step1 := by apply Matrix.ext; change ∀ i j, raw9805step2 i j = -(raw9805step1 i j); unfold raw9805step2 raw9805step1; decide +kernel
      have hl : raw9805step2Labels = raw9805step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9805step2 raw9805step2Labels = mixedMoment B raw9805step3 raw9805step3Labels := by
      have ha : raw9805step3 = raw9805step2 := by apply Matrix.ext; unfold raw9805step3 raw9805step2; decide +kernel
      have hl : raw9805step2Labels = labelEmbedding1 ∘ raw9805step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9805step2 raw9805step2Labels raw9805step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3294 node3294Labels := by rfl

def raw9806 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9806Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9806step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9806step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9806step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw9806step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9806step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw9806step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9806step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw9806step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9806 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9806 raw9806Labels = mixedMoment B node3578 node3578Labels := by
  calc
    mixedMoment B raw9806 raw9806Labels = mixedMoment B raw9806step0 raw9806step0Labels := by
      have hz : ∀ j, raw9806 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9806step0 = (fun i j => raw9806 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9806step0 raw9806; decide +kernel
      have hl : raw9806step0Labels = raw9806Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9806 raw9806Labels permutation346 hz
    mixedMoment B raw9806step0 raw9806step0Labels = mixedMoment B raw9806step1 raw9806step1Labels := by
      have ha : raw9806step1 = (fun i j => raw9806step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9806step1 raw9806step0; decide +kernel
      have hl : raw9806step1Labels = raw9806step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9806step0 raw9806step0Labels permutation38 permutation7
    mixedMoment B raw9806step1 raw9806step1Labels = mixedMoment B raw9806step2 raw9806step2Labels := by
      have ha : raw9806step2 = -raw9806step1 := by apply Matrix.ext; change ∀ i j, raw9806step2 i j = -(raw9806step1 i j); unfold raw9806step2 raw9806step1; decide +kernel
      have hl : raw9806step2Labels = raw9806step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9806step2 raw9806step2Labels = mixedMoment B raw9806step3 raw9806step3Labels := by
      have ha : raw9806step3 = raw9806step2 := by apply Matrix.ext; unfold raw9806step3 raw9806step2; decide +kernel
      have hl : raw9806step2Labels = labelEmbedding1 ∘ raw9806step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9806step2 raw9806step2Labels raw9806step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3578 node3578Labels := by rfl

def raw9807 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9807Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9807step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw9807step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9807step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw9807step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9807step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw9807step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9807 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9807 raw9807Labels = mixedMoment B node3562 node3562Labels := by
  calc
    mixedMoment B raw9807 raw9807Labels = mixedMoment B raw9807step0 raw9807step0Labels := by
      have ha : raw9807step0 = (fun i j => raw9807 (permutation206 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9807step0 raw9807; decide +kernel
      have hl : raw9807step0Labels = raw9807Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9807 raw9807Labels permutation206 permutation7
    mixedMoment B raw9807step0 raw9807step0Labels = mixedMoment B raw9807step1 raw9807step1Labels := by
      have ha : raw9807step1 = -raw9807step0 := by apply Matrix.ext; change ∀ i j, raw9807step1 i j = -(raw9807step0 i j); unfold raw9807step1 raw9807step0; decide +kernel
      have hl : raw9807step1Labels = raw9807step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9807step1 raw9807step1Labels = mixedMoment B raw9807step2 raw9807step2Labels := by
      have ha : raw9807step2 = raw9807step1 := by apply Matrix.ext; unfold raw9807step2 raw9807step1; decide +kernel
      have hl : raw9807step1Labels = labelEmbedding1 ∘ raw9807step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9807step1 raw9807step1Labels raw9807step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3562 node3562Labels := by rfl

def raw9808 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![0, 1, -1], ![2, -1, -1]]
def raw9808Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9808step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![0, 1, -1], ![2, -1, -1]]
def raw9808step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9808step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw9808step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9808step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw9808step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9808step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw9808step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9808 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9808 raw9808Labels = mixedMoment B node3580 node3580Labels := by
  calc
    mixedMoment B raw9808 raw9808Labels = mixedMoment B raw9808step0 raw9808step0Labels := by
      have hz : ∀ j, raw9808 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9808step0 = (fun i j => raw9808 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9808step0 raw9808; decide +kernel
      have hl : raw9808step0Labels = raw9808Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9808 raw9808Labels permutation346 hz
    mixedMoment B raw9808step0 raw9808step0Labels = mixedMoment B raw9808step1 raw9808step1Labels := by
      have ha : raw9808step1 = (fun i j => raw9808step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9808step1 raw9808step0; decide +kernel
      have hl : raw9808step1Labels = raw9808step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9808step0 raw9808step0Labels permutation38 permutation7
    mixedMoment B raw9808step1 raw9808step1Labels = mixedMoment B raw9808step2 raw9808step2Labels := by
      have ha : raw9808step2 = -raw9808step1 := by apply Matrix.ext; change ∀ i j, raw9808step2 i j = -(raw9808step1 i j); unfold raw9808step2 raw9808step1; decide +kernel
      have hl : raw9808step2Labels = raw9808step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9808step2 raw9808step2Labels = mixedMoment B raw9808step3 raw9808step3Labels := by
      have ha : raw9808step3 = raw9808step2 := by apply Matrix.ext; unfold raw9808step3 raw9808step2; decide +kernel
      have hl : raw9808step2Labels = labelEmbedding1 ∘ raw9808step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9808step2 raw9808step2Labels raw9808step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3580 node3580Labels := by rfl

def raw9809 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw9809Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9809step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw9809step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9809step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw9809step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9809step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw9809step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9809step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw9809step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9809 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9809 raw9809Labels = mixedMoment B node3581 node3581Labels := by
  calc
    mixedMoment B raw9809 raw9809Labels = mixedMoment B raw9809step0 raw9809step0Labels := by
      have hz : ∀ j, raw9809 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9809step0 = (fun i j => raw9809 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9809step0 raw9809; decide +kernel
      have hl : raw9809step0Labels = raw9809Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9809 raw9809Labels permutation346 hz
    mixedMoment B raw9809step0 raw9809step0Labels = mixedMoment B raw9809step1 raw9809step1Labels := by
      have ha : raw9809step1 = (fun i j => raw9809step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9809step1 raw9809step0; decide +kernel
      have hl : raw9809step1Labels = raw9809step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9809step0 raw9809step0Labels permutation38 permutation7
    mixedMoment B raw9809step1 raw9809step1Labels = mixedMoment B raw9809step2 raw9809step2Labels := by
      have ha : raw9809step2 = -raw9809step1 := by apply Matrix.ext; change ∀ i j, raw9809step2 i j = -(raw9809step1 i j); unfold raw9809step2 raw9809step1; decide +kernel
      have hl : raw9809step2Labels = raw9809step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9809step2 raw9809step2Labels = mixedMoment B raw9809step3 raw9809step3Labels := by
      have ha : raw9809step3 = raw9809step2 := by apply Matrix.ext; unfold raw9809step3 raw9809step2; decide +kernel
      have hl : raw9809step2Labels = labelEmbedding1 ∘ raw9809step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9809step2 raw9809step2Labels raw9809step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3581 node3581Labels := by rfl

def raw9810 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw9810Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9810step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw9810step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9810step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw9810step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9810step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw9810step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9810step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw9810step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9810 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9810 raw9810Labels = mixedMoment B node3297 node3297Labels := by
  calc
    mixedMoment B raw9810 raw9810Labels = mixedMoment B raw9810step0 raw9810step0Labels := by
      have hz : ∀ j, raw9810 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9810step0 = (fun i j => raw9810 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9810step0 raw9810; decide +kernel
      have hl : raw9810step0Labels = raw9810Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9810 raw9810Labels permutation346 hz
    mixedMoment B raw9810step0 raw9810step0Labels = mixedMoment B raw9810step1 raw9810step1Labels := by
      have ha : raw9810step1 = (fun i j => raw9810step0 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw9810step1 raw9810step0; decide +kernel
      have hl : raw9810step1Labels = raw9810step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9810step0 raw9810step0Labels permutation32 permutation5
    mixedMoment B raw9810step1 raw9810step1Labels = mixedMoment B raw9810step2 raw9810step2Labels := by
      have ha : raw9810step2 = -raw9810step1 := by apply Matrix.ext; change ∀ i j, raw9810step2 i j = -(raw9810step1 i j); unfold raw9810step2 raw9810step1; decide +kernel
      have hl : raw9810step2Labels = raw9810step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9810step2 raw9810step2Labels = mixedMoment B raw9810step3 raw9810step3Labels := by
      have ha : raw9810step3 = raw9810step2 := by apply Matrix.ext; unfold raw9810step3 raw9810step2; decide +kernel
      have hl : raw9810step2Labels = labelEmbedding1 ∘ raw9810step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9810step2 raw9810step2Labels raw9810step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3297 node3297Labels := by rfl

def raw9811 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw9811Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9811step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw9811step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9811step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 2, -1], ![-1, -1, 2], ![-1, -1, 2]]
def raw9811step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9811step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw9811step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9811step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw9811step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9811 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9811 raw9811Labels = mixedMoment B node3542 node3542Labels := by
  calc
    mixedMoment B raw9811 raw9811Labels = mixedMoment B raw9811step0 raw9811step0Labels := by
      have hz : ∀ j, raw9811 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9811step0 = (fun i j => raw9811 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9811step0 raw9811; decide +kernel
      have hl : raw9811step0Labels = raw9811Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9811 raw9811Labels permutation346 hz
    mixedMoment B raw9811step0 raw9811step0Labels = mixedMoment B raw9811step1 raw9811step1Labels := by
      have ha : raw9811step1 = (fun i j => raw9811step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9811step1 raw9811step0; decide +kernel
      have hl : raw9811step1Labels = raw9811step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9811step0 raw9811step0Labels permutation38 permutation7
    mixedMoment B raw9811step1 raw9811step1Labels = mixedMoment B raw9811step2 raw9811step2Labels := by
      have ha : raw9811step2 = -raw9811step1 := by apply Matrix.ext; change ∀ i j, raw9811step2 i j = -(raw9811step1 i j); unfold raw9811step2 raw9811step1; decide +kernel
      have hl : raw9811step2Labels = raw9811step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9811step2 raw9811step2Labels = mixedMoment B raw9811step3 raw9811step3Labels := by
      have ha : raw9811step3 = raw9811step2 := by apply Matrix.ext; unfold raw9811step3 raw9811step2; decide +kernel
      have hl : raw9811step2Labels = labelEmbedding1 ∘ raw9811step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9811step2 raw9811step2Labels raw9811step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3542 node3542Labels := by rfl

def raw9812 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw9812Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9812step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw9812step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9812step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw9812step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9812step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw9812step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9812 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9812 raw9812Labels = mixedMoment B node3520 node3520Labels := by
  calc
    mixedMoment B raw9812 raw9812Labels = mixedMoment B raw9812step0 raw9812step0Labels := by
      have ha : raw9812step0 = (fun i j => raw9812 (permutation206 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9812step0 raw9812; decide +kernel
      have hl : raw9812step0Labels = raw9812Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9812 raw9812Labels permutation206 permutation7
    mixedMoment B raw9812step0 raw9812step0Labels = mixedMoment B raw9812step1 raw9812step1Labels := by
      have ha : raw9812step1 = -raw9812step0 := by apply Matrix.ext; change ∀ i j, raw9812step1 i j = -(raw9812step0 i j); unfold raw9812step1 raw9812step0; decide +kernel
      have hl : raw9812step1Labels = raw9812step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9812step1 raw9812step1Labels = mixedMoment B raw9812step2 raw9812step2Labels := by
      have ha : raw9812step2 = raw9812step1 := by apply Matrix.ext; unfold raw9812step2 raw9812step1; decide +kernel
      have hl : raw9812step1Labels = labelEmbedding1 ∘ raw9812step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9812step1 raw9812step1Labels raw9812step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3520 node3520Labels := by rfl

def raw9813 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![2, -1, -1], ![2, -1, -1]]
def raw9813Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9813step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 0, 1], ![2, -1, -1], ![2, -1, -1]]
def raw9813step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9813step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw9813step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9813step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw9813step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9813step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw9813step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9813 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9813 raw9813Labels = mixedMoment B node3482 node3482Labels := by
  calc
    mixedMoment B raw9813 raw9813Labels = mixedMoment B raw9813step0 raw9813step0Labels := by
      have hz : ∀ j, raw9813 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9813step0 = (fun i j => raw9813 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9813step0 raw9813; decide +kernel
      have hl : raw9813step0Labels = raw9813Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9813 raw9813Labels permutation346 hz
    mixedMoment B raw9813step0 raw9813step0Labels = mixedMoment B raw9813step1 raw9813step1Labels := by
      have ha : raw9813step1 = (fun i j => raw9813step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9813step1 raw9813step0; decide +kernel
      have hl : raw9813step1Labels = raw9813step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9813step0 raw9813step0Labels permutation38 permutation7
    mixedMoment B raw9813step1 raw9813step1Labels = mixedMoment B raw9813step2 raw9813step2Labels := by
      have ha : raw9813step2 = -raw9813step1 := by apply Matrix.ext; change ∀ i j, raw9813step2 i j = -(raw9813step1 i j); unfold raw9813step2 raw9813step1; decide +kernel
      have hl : raw9813step2Labels = raw9813step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9813step2 raw9813step2Labels = mixedMoment B raw9813step3 raw9813step3Labels := by
      have ha : raw9813step3 = raw9813step2 := by apply Matrix.ext; unfold raw9813step3 raw9813step2; decide +kernel
      have hl : raw9813step2Labels = labelEmbedding1 ∘ raw9813step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9813step2 raw9813step2Labels raw9813step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3482 node3482Labels := by rfl

def raw9814 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1]]
def raw9814Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9814step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1]]
def raw9814step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9814step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw9814step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9814step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw9814step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9814step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw9814step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9814 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9814 raw9814Labels = mixedMoment B node3544 node3544Labels := by
  calc
    mixedMoment B raw9814 raw9814Labels = mixedMoment B raw9814step0 raw9814step0Labels := by
      have hz : ∀ j, raw9814 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9814step0 = (fun i j => raw9814 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9814step0 raw9814; decide +kernel
      have hl : raw9814step0Labels = raw9814Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9814 raw9814Labels permutation346 hz
    mixedMoment B raw9814step0 raw9814step0Labels = mixedMoment B raw9814step1 raw9814step1Labels := by
      have ha : raw9814step1 = (fun i j => raw9814step0 (permutation39 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9814step1 raw9814step0; decide +kernel
      have hl : raw9814step1Labels = raw9814step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9814step0 raw9814step0Labels permutation39 permutation7
    mixedMoment B raw9814step1 raw9814step1Labels = mixedMoment B raw9814step2 raw9814step2Labels := by
      have ha : raw9814step2 = -raw9814step1 := by apply Matrix.ext; change ∀ i j, raw9814step2 i j = -(raw9814step1 i j); unfold raw9814step2 raw9814step1; decide +kernel
      have hl : raw9814step2Labels = raw9814step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9814step2 raw9814step2Labels = mixedMoment B raw9814step3 raw9814step3Labels := by
      have ha : raw9814step3 = raw9814step2 := by apply Matrix.ext; unfold raw9814step3 raw9814step2; decide +kernel
      have hl : raw9814step2Labels = labelEmbedding1 ∘ raw9814step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9814step2 raw9814step2Labels raw9814step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3544 node3544Labels := by rfl

def raw9815 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw9815Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9815step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw9815step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9815step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, -1, 3]]
def raw9815step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9815step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw9815step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9815step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw9815step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9815 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9815 raw9815Labels = mixedMoment B node3291 node3291Labels := by
  calc
    mixedMoment B raw9815 raw9815Labels = mixedMoment B raw9815step0 raw9815step0Labels := by
      have hz : ∀ j, raw9815 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9815step0 = (fun i j => raw9815 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9815step0 raw9815; decide +kernel
      have hl : raw9815step0Labels = raw9815Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9815 raw9815Labels permutation346 hz
    mixedMoment B raw9815step0 raw9815step0Labels = mixedMoment B raw9815step1 raw9815step1Labels := by
      have ha : raw9815step1 = (fun i j => raw9815step0 (permutation34 i) (permutation5 j)) := by apply Matrix.ext; unfold raw9815step1 raw9815step0; decide +kernel
      have hl : raw9815step1Labels = raw9815step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9815step0 raw9815step0Labels permutation34 permutation5
    mixedMoment B raw9815step1 raw9815step1Labels = mixedMoment B raw9815step2 raw9815step2Labels := by
      have ha : raw9815step2 = -raw9815step1 := by apply Matrix.ext; change ∀ i j, raw9815step2 i j = -(raw9815step1 i j); unfold raw9815step2 raw9815step1; decide +kernel
      have hl : raw9815step2Labels = raw9815step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9815step2 raw9815step2Labels = mixedMoment B raw9815step3 raw9815step3Labels := by
      have ha : raw9815step3 = raw9815step2 := by apply Matrix.ext; unfold raw9815step3 raw9815step2; decide +kernel
      have hl : raw9815step2Labels = labelEmbedding1 ∘ raw9815step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9815step2 raw9815step2Labels raw9815step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3291 node3291Labels := by rfl

def raw9816 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw9816Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9816step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw9816step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9816step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw9816step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9816step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw9816step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9816 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9816 raw9816Labels = mixedMoment B node3523 node3523Labels := by
  calc
    mixedMoment B raw9816 raw9816Labels = mixedMoment B raw9816step0 raw9816step0Labels := by
      have hz : ∀ j, raw9816 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9816step0 = (fun i j => raw9816 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9816step0 raw9816; decide +kernel
      have hl : raw9816step0Labels = raw9816Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9816 raw9816Labels permutation346 hz
    mixedMoment B raw9816step0 raw9816step0Labels = mixedMoment B raw9816step1 raw9816step1Labels := by
      have ha : raw9816step1 = (fun i j => raw9816step0 (permutation144 i) (permutation5 j)) := by apply Matrix.ext; unfold raw9816step1 raw9816step0; decide +kernel
      have hl : raw9816step1Labels = raw9816step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9816step0 raw9816step0Labels permutation144 permutation5
    mixedMoment B raw9816step1 raw9816step1Labels = mixedMoment B raw9816step2 raw9816step2Labels := by
      have ha : raw9816step2 = raw9816step1 := by apply Matrix.ext; unfold raw9816step2 raw9816step1; decide +kernel
      have hl : raw9816step1Labels = labelEmbedding1 ∘ raw9816step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9816step1 raw9816step1Labels raw9816step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3523 node3523Labels := by rfl

def raw9817 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw9817Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9817step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw9817step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9817step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw9817step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9817 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9817 raw9817Labels = mixedMoment B node3519 node3519Labels := by
  calc
    mixedMoment B raw9817 raw9817Labels = mixedMoment B raw9817step0 raw9817step0Labels := by
      have ha : raw9817step0 = (fun i j => raw9817 (permutation662 i) (permutation5 j)) := by apply Matrix.ext; unfold raw9817step0 raw9817; decide +kernel
      have hl : raw9817step0Labels = raw9817Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9817 raw9817Labels permutation662 permutation5
    mixedMoment B raw9817step0 raw9817step0Labels = mixedMoment B raw9817step1 raw9817step1Labels := by
      have ha : raw9817step1 = raw9817step0 := by apply Matrix.ext; unfold raw9817step1 raw9817step0; decide +kernel
      have hl : raw9817step0Labels = labelEmbedding1 ∘ raw9817step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9817step0 raw9817step0Labels raw9817step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3519 node3519Labels := by rfl

def raw9818 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -2, -1]]
def raw9818Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9818step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 0, 1], ![1, 0, -1], ![3, -2, -1]]
def raw9818step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9818step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw9818step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9818step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw9818step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9818step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw9818step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9818 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9818 raw9818Labels = mixedMoment B node3481 node3481Labels := by
  calc
    mixedMoment B raw9818 raw9818Labels = mixedMoment B raw9818step0 raw9818step0Labels := by
      have hz : ∀ j, raw9818 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9818step0 = (fun i j => raw9818 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9818step0 raw9818; decide +kernel
      have hl : raw9818step0Labels = raw9818Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9818 raw9818Labels permutation346 hz
    mixedMoment B raw9818step0 raw9818step0Labels = mixedMoment B raw9818step1 raw9818step1Labels := by
      have ha : raw9818step1 = (fun i j => raw9818step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9818step1 raw9818step0; decide +kernel
      have hl : raw9818step1Labels = raw9818step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9818step0 raw9818step0Labels permutation38 permutation7
    mixedMoment B raw9818step1 raw9818step1Labels = mixedMoment B raw9818step2 raw9818step2Labels := by
      have ha : raw9818step2 = -raw9818step1 := by apply Matrix.ext; change ∀ i j, raw9818step2 i j = -(raw9818step1 i j); unfold raw9818step2 raw9818step1; decide +kernel
      have hl : raw9818step2Labels = raw9818step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9818step2 raw9818step2Labels = mixedMoment B raw9818step3 raw9818step3Labels := by
      have ha : raw9818step3 = raw9818step2 := by apply Matrix.ext; unfold raw9818step3 raw9818step2; decide +kernel
      have hl : raw9818step2Labels = labelEmbedding1 ∘ raw9818step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9818step2 raw9818step2Labels raw9818step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3481 node3481Labels := by rfl

def raw9819 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![3, -2, -1]]
def raw9819Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9819step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![0, 1, -1], ![3, -2, -1]]
def raw9819step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9819step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw9819step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9819step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw9819step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9819 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9819 raw9819Labels = mixedMoment B node3543 node3543Labels := by
  calc
    mixedMoment B raw9819 raw9819Labels = mixedMoment B raw9819step0 raw9819step0Labels := by
      have hz : ∀ j, raw9819 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9819step0 = (fun i j => raw9819 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9819step0 raw9819; decide +kernel
      have hl : raw9819step0Labels = raw9819Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9819 raw9819Labels permutation346 hz
    mixedMoment B raw9819step0 raw9819step0Labels = mixedMoment B raw9819step1 raw9819step1Labels := by
      have ha : raw9819step1 = (fun i j => raw9819step0 (permutation143 i) (permutation5 j)) := by apply Matrix.ext; unfold raw9819step1 raw9819step0; decide +kernel
      have hl : raw9819step1Labels = raw9819step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9819step0 raw9819step0Labels permutation143 permutation5
    mixedMoment B raw9819step1 raw9819step1Labels = mixedMoment B raw9819step2 raw9819step2Labels := by
      have ha : raw9819step2 = raw9819step1 := by apply Matrix.ext; unfold raw9819step2 raw9819step1; decide +kernel
      have hl : raw9819step1Labels = labelEmbedding1 ∘ raw9819step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9819step1 raw9819step1Labels raw9819step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3543 node3543Labels := by rfl

def raw9820 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9820Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9820step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9820step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9820step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9820step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9820 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9820 raw9820Labels = mixedMoment B node2723 node2723Labels := by
  calc
    mixedMoment B raw9820 raw9820Labels = mixedMoment B raw9820step0 raw9820step0Labels := by
      have hz : ∀ j, raw9820 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9820step0 = (fun i j => raw9820 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9820step0 raw9820; decide +kernel
      have hl : raw9820step0Labels = raw9820Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9820 raw9820Labels permutation346 hz
    mixedMoment B raw9820step0 raw9820step0Labels = mixedMoment B raw9820step1 raw9820step1Labels := by
      have ha : raw9820step1 = (fun i j => raw9820step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9820step1 raw9820step0; decide +kernel
      have hl : raw9820step1Labels = raw9820step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9820step0 raw9820step0Labels permutation38 permutation2
    _ = mixedMoment B node2723 node2723Labels := by rfl

def raw9821 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9821Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9821step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9821step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9821 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9821 raw9821Labels = mixedMoment B node3876 node3876Labels := by
  calc
    mixedMoment B raw9821 raw9821Labels = mixedMoment B raw9821step0 raw9821step0Labels := by
      have hz : ∀ j, raw9821 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9821step0 = (fun i j => raw9821 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9821step0 raw9821; decide +kernel
      have hl : raw9821step0Labels = raw9821Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9821 raw9821Labels permutation346 hz
    _ = mixedMoment B node3876 node3876Labels := by rfl

def raw9822 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9822Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9822step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9822step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9822 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9822 raw9822Labels = mixedMoment B node3838 node3838Labels := by
  calc
    mixedMoment B raw9822 raw9822Labels = mixedMoment B raw9822step0 raw9822step0Labels := by
      have ha : raw9822step0 = (fun i j => raw9822 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9822step0 raw9822; decide +kernel
      have hl : raw9822step0Labels = raw9822Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9822 raw9822Labels permutation182 permutation2
    _ = mixedMoment B node3838 node3838Labels := by rfl

def raw9823 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9823Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9823step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9823step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9823step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9823step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9823 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9823 raw9823Labels = mixedMoment B node3808 node3808Labels := by
  calc
    mixedMoment B raw9823 raw9823Labels = mixedMoment B raw9823step0 raw9823step0Labels := by
      have hz : ∀ j, raw9823 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9823step0 = (fun i j => raw9823 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9823step0 raw9823; decide +kernel
      have hl : raw9823step0Labels = raw9823Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9823 raw9823Labels permutation346 hz
    mixedMoment B raw9823step0 raw9823step0Labels = mixedMoment B raw9823step1 raw9823step1Labels := by
      have ha : raw9823step1 = (fun i j => raw9823step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9823step1 raw9823step0; decide +kernel
      have hl : raw9823step1Labels = raw9823step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9823step0 raw9823step0Labels permutation38 permutation2
    _ = mixedMoment B node3808 node3808Labels := by rfl

def raw9824 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw9824Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9824step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw9824step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9824step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw9824step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9824 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9824 raw9824Labels = mixedMoment B node3902 node3902Labels := by
  calc
    mixedMoment B raw9824 raw9824Labels = mixedMoment B raw9824step0 raw9824step0Labels := by
      have hz : ∀ j, raw9824 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9824step0 = (fun i j => raw9824 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9824step0 raw9824; decide +kernel
      have hl : raw9824step0Labels = raw9824Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9824 raw9824Labels permutation346 hz
    mixedMoment B raw9824step0 raw9824step0Labels = mixedMoment B raw9824step1 raw9824step1Labels := by
      have ha : raw9824step1 = (fun i j => raw9824step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9824step1 raw9824step0; decide +kernel
      have hl : raw9824step1Labels = raw9824step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9824step0 raw9824step0Labels permutation38 permutation2
    _ = mixedMoment B node3902 node3902Labels := by rfl

def raw9825 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw9825Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9825step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw9825step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9825step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw9825step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9825 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9825 raw9825Labels = mixedMoment B node3904 node3904Labels := by
  calc
    mixedMoment B raw9825 raw9825Labels = mixedMoment B raw9825step0 raw9825step0Labels := by
      have hz : ∀ j, raw9825 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9825step0 = (fun i j => raw9825 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9825step0 raw9825; decide +kernel
      have hl : raw9825step0Labels = raw9825Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9825 raw9825Labels permutation346 hz
    mixedMoment B raw9825step0 raw9825step0Labels = mixedMoment B raw9825step1 raw9825step1Labels := by
      have ha : raw9825step1 = (fun i j => raw9825step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9825step1 raw9825step0; decide +kernel
      have hl : raw9825step1Labels = raw9825step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9825step0 raw9825step0Labels permutation38 permutation2
    _ = mixedMoment B node3904 node3904Labels := by rfl

def raw9826 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![0, 0], ![-1, 1], ![1, -1], ![1, -1]]
def raw9826Labels : Fin 2 → Fin 2 := ![0, 1]

def raw9826step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![-1, 1], ![1, -1], ![1, -1]]
def raw9826step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw9826step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw9826step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical9826 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9826 raw9826Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw9826 raw9826Labels = mixedMoment B raw9826step0 raw9826step0Labels := by
      have hz : ∀ j, raw9826 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9826step0 = (fun i j => raw9826 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9826step0 raw9826; decide +kernel
      have hl : raw9826step0Labels = raw9826Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9826 raw9826Labels permutation346 hz
    mixedMoment B raw9826step0 raw9826step0Labels = mixedMoment B raw9826step1 raw9826step1Labels := by
      have ha : raw9826step1 = (fun i j => raw9826step0 (permutation38 i) (permutation0 j)) := by apply Matrix.ext; unfold raw9826step1 raw9826step0; decide +kernel
      have hl : raw9826step1Labels = raw9826step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9826step0 raw9826step0Labels permutation38 permutation0
    _ = mixedMoment B node4091 node4091Labels := by rfl

def raw9827 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9827Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9827step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9827step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9827step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9827step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9827 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9827 raw9827Labels = mixedMoment B node1240 node1240Labels := by
  calc
    mixedMoment B raw9827 raw9827Labels = mixedMoment B raw9827step0 raw9827step0Labels := by
      have hz : ∀ j, raw9827 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9827step0 = (fun i j => raw9827 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9827step0 raw9827; decide +kernel
      have hl : raw9827step0Labels = raw9827Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9827 raw9827Labels permutation346 hz
    mixedMoment B raw9827step0 raw9827step0Labels = mixedMoment B raw9827step1 raw9827step1Labels := by
      have ha : raw9827step1 = (fun i j => raw9827step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9827step1 raw9827step0; decide +kernel
      have hl : raw9827step1Labels = raw9827step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9827step0 raw9827step0Labels permutation38 permutation2
    _ = mixedMoment B node1240 node1240Labels := by rfl

def raw9828 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9828Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9828step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw9828step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9828 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9828 raw9828Labels = mixedMoment B node1213 node1213Labels := by
  calc
    mixedMoment B raw9828 raw9828Labels = mixedMoment B raw9828step0 raw9828step0Labels := by
      have ha : raw9828step0 = (fun i j => raw9828 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9828step0 raw9828; decide +kernel
      have hl : raw9828step0Labels = raw9828Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9828 raw9828Labels permutation200 permutation2
    _ = mixedMoment B node1213 node1213Labels := by rfl

def raw9829 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9829Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9829step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9829step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9829 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9829 raw9829Labels = mixedMoment B node1262 node1262Labels := by
  calc
    mixedMoment B raw9829 raw9829Labels = mixedMoment B raw9829step0 raw9829step0Labels := by
      have hz : ∀ j, raw9829 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9829step0 = (fun i j => raw9829 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9829step0 raw9829; decide +kernel
      have hl : raw9829step0Labels = raw9829Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9829 raw9829Labels permutation346 hz
    _ = mixedMoment B node1262 node1262Labels := by rfl

def raw9830 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw9830Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9830step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw9830step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9830step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw9830step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9830 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9830 raw9830Labels = mixedMoment B node1220 node1220Labels := by
  calc
    mixedMoment B raw9830 raw9830Labels = mixedMoment B raw9830step0 raw9830step0Labels := by
      have hz : ∀ j, raw9830 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9830step0 = (fun i j => raw9830 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9830step0 raw9830; decide +kernel
      have hl : raw9830step0Labels = raw9830Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9830 raw9830Labels permutation346 hz
    mixedMoment B raw9830step0 raw9830step0Labels = mixedMoment B raw9830step1 raw9830step1Labels := by
      have ha : raw9830step1 = (fun i j => raw9830step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9830step1 raw9830step0; decide +kernel
      have hl : raw9830step1Labels = raw9830step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9830step0 raw9830step0Labels permutation38 permutation2
    _ = mixedMoment B node1220 node1220Labels := by rfl

def raw9831 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw9831Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9831step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw9831step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9831step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw9831step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9831 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9831 raw9831Labels = mixedMoment B node1217 node1217Labels := by
  calc
    mixedMoment B raw9831 raw9831Labels = mixedMoment B raw9831step0 raw9831step0Labels := by
      have hz : ∀ j, raw9831 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9831step0 = (fun i j => raw9831 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9831step0 raw9831; decide +kernel
      have hl : raw9831step0Labels = raw9831Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9831 raw9831Labels permutation346 hz
    mixedMoment B raw9831step0 raw9831step0Labels = mixedMoment B raw9831step1 raw9831step1Labels := by
      have ha : raw9831step1 = (fun i j => raw9831step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9831step1 raw9831step0; decide +kernel
      have hl : raw9831step1Labels = raw9831step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9831step0 raw9831step0Labels permutation38 permutation2
    _ = mixedMoment B node1217 node1217Labels := by rfl

def raw9832 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9832Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9832step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9832step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9832 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9832 raw9832Labels = mixedMoment B node2556 node2556Labels := by
  calc
    mixedMoment B raw9832 raw9832Labels = mixedMoment B raw9832step0 raw9832step0Labels := by
      have ha : raw9832step0 = (fun i j => raw9832 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9832step0 raw9832; decide +kernel
      have hl : raw9832step0Labels = raw9832Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9832 raw9832Labels permutation182 permutation2
    _ = mixedMoment B node2556 node2556Labels := by rfl

def raw9833 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9833Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9833step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9833step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9833step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9833step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9833 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9833 raw9833Labels = mixedMoment B node2514 node2514Labels := by
  calc
    mixedMoment B raw9833 raw9833Labels = mixedMoment B raw9833step0 raw9833step0Labels := by
      have hz : ∀ j, raw9833 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9833step0 = (fun i j => raw9833 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9833step0 raw9833; decide +kernel
      have hl : raw9833step0Labels = raw9833Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9833 raw9833Labels permutation346 hz
    mixedMoment B raw9833step0 raw9833step0Labels = mixedMoment B raw9833step1 raw9833step1Labels := by
      have ha : raw9833step1 = (fun i j => raw9833step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9833step1 raw9833step0; decide +kernel
      have hl : raw9833step1Labels = raw9833step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9833step0 raw9833step0Labels permutation38 permutation2
    _ = mixedMoment B node2514 node2514Labels := by rfl

def raw9834 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw9834Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9834step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw9834step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9834step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9834step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9834 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9834 raw9834Labels = mixedMoment B node2723 node2723Labels := by
  calc
    mixedMoment B raw9834 raw9834Labels = mixedMoment B raw9834step0 raw9834step0Labels := by
      have hz : ∀ j, raw9834 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9834step0 = (fun i j => raw9834 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9834step0 raw9834; decide +kernel
      have hl : raw9834step0Labels = raw9834Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9834 raw9834Labels permutation346 hz
    mixedMoment B raw9834step0 raw9834step0Labels = mixedMoment B raw9834step1 raw9834step1Labels := by
      have ha : raw9834step1 = (fun i j => raw9834step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9834step1 raw9834step0; decide +kernel
      have hl : raw9834step1Labels = raw9834step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9834step0 raw9834step0Labels permutation40 permutation2
    _ = mixedMoment B node2723 node2723Labels := by rfl

def raw9835 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw9835Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9835step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw9835step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9835step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw9835step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9835 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9835 raw9835Labels = mixedMoment B node2741 node2741Labels := by
  calc
    mixedMoment B raw9835 raw9835Labels = mixedMoment B raw9835step0 raw9835step0Labels := by
      have hz : ∀ j, raw9835 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9835step0 = (fun i j => raw9835 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9835step0 raw9835; decide +kernel
      have hl : raw9835step0Labels = raw9835Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9835 raw9835Labels permutation346 hz
    mixedMoment B raw9835step0 raw9835step0Labels = mixedMoment B raw9835step1 raw9835step1Labels := by
      have ha : raw9835step1 = (fun i j => raw9835step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9835step1 raw9835step0; decide +kernel
      have hl : raw9835step1Labels = raw9835step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9835step0 raw9835step0Labels permutation38 permutation2
    _ = mixedMoment B node2741 node2741Labels := by rfl

def raw9836 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9836Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9836step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw9836step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9836 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9836 raw9836Labels = mixedMoment B node2615 node2615Labels := by
  calc
    mixedMoment B raw9836 raw9836Labels = mixedMoment B raw9836step0 raw9836step0Labels := by
      have ha : raw9836step0 = (fun i j => raw9836 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9836step0 raw9836; decide +kernel
      have hl : raw9836step0Labels = raw9836Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9836 raw9836Labels permutation158 permutation2
    _ = mixedMoment B node2615 node2615Labels := by rfl

def raw9837 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9837Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9837step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9837step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9837 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9837 raw9837Labels = mixedMoment B node2633 node2633Labels := by
  calc
    mixedMoment B raw9837 raw9837Labels = mixedMoment B raw9837step0 raw9837step0Labels := by
      have hz : ∀ j, raw9837 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9837step0 = (fun i j => raw9837 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9837step0 raw9837; decide +kernel
      have hl : raw9837step0Labels = raw9837Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9837 raw9837Labels permutation346 hz
    _ = mixedMoment B node2633 node2633Labels := by rfl

def raw9838 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw9838Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9838step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw9838step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9838 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9838 raw9838Labels = mixedMoment B node2621 node2621Labels := by
  calc
    mixedMoment B raw9838 raw9838Labels = mixedMoment B raw9838step0 raw9838step0Labels := by
      have hz : ∀ j, raw9838 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9838step0 = (fun i j => raw9838 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9838step0 raw9838; decide +kernel
      have hl : raw9838step0Labels = raw9838Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9838 raw9838Labels permutation346 hz
    _ = mixedMoment B node2621 node2621Labels := by rfl

def raw9839 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw9839Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9839step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw9839step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9839 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9839 raw9839Labels = mixedMoment B node2618 node2618Labels := by
  calc
    mixedMoment B raw9839 raw9839Labels = mixedMoment B raw9839step0 raw9839step0Labels := by
      have hz : ∀ j, raw9839 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9839step0 = (fun i j => raw9839 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9839step0 raw9839; decide +kernel
      have hl : raw9839step0Labels = raw9839Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9839 raw9839Labels permutation346 hz
    _ = mixedMoment B node2618 node2618Labels := by rfl

def raw9840 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9840Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9840step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9840step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9840 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9840 raw9840Labels = mixedMoment B node2567 node2567Labels := by
  calc
    mixedMoment B raw9840 raw9840Labels = mixedMoment B raw9840step0 raw9840step0Labels := by
      have ha : raw9840step0 = (fun i j => raw9840 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9840step0 raw9840; decide +kernel
      have hl : raw9840step0Labels = raw9840Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9840 raw9840Labels permutation176 permutation2
    _ = mixedMoment B node2567 node2567Labels := by rfl

def raw9841 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw9841Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9841step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw9841step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9841 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9841 raw9841Labels = mixedMoment B node2546 node2546Labels := by
  calc
    mixedMoment B raw9841 raw9841Labels = mixedMoment B raw9841step0 raw9841step0Labels := by
      have ha : raw9841step0 = (fun i j => raw9841 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9841step0 raw9841; decide +kernel
      have hl : raw9841step0Labels = raw9841Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9841 raw9841Labels permutation182 permutation2
    _ = mixedMoment B node2546 node2546Labels := by rfl

def raw9842 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw9842Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9842step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw9842step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9842 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9842 raw9842Labels = mixedMoment B node2543 node2543Labels := by
  calc
    mixedMoment B raw9842 raw9842Labels = mixedMoment B raw9842step0 raw9842step0Labels := by
      have ha : raw9842step0 = (fun i j => raw9842 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9842step0 raw9842; decide +kernel
      have hl : raw9842step0Labels = raw9842Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9842 raw9842Labels permutation182 permutation2
    _ = mixedMoment B node2543 node2543Labels := by rfl

def raw9843 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9843Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9843step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw9843step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9843 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9843 raw9843Labels = mixedMoment B node2480 node2480Labels := by
  calc
    mixedMoment B raw9843 raw9843Labels = mixedMoment B raw9843step0 raw9843step0Labels := by
      have ha : raw9843step0 = (fun i j => raw9843 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9843step0 raw9843; decide +kernel
      have hl : raw9843step0Labels = raw9843Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9843 raw9843Labels permutation200 permutation2
    _ = mixedMoment B node2480 node2480Labels := by rfl

def raw9844 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![2, -1, -1], ![2, -1, -1]]
def raw9844Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9844step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 0, 1], ![2, -1, -1], ![2, -1, -1]]
def raw9844step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9844step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw9844step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9844 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9844 raw9844Labels = mixedMoment B node2489 node2489Labels := by
  calc
    mixedMoment B raw9844 raw9844Labels = mixedMoment B raw9844step0 raw9844step0Labels := by
      have hz : ∀ j, raw9844 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9844step0 = (fun i j => raw9844 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9844step0 raw9844; decide +kernel
      have hl : raw9844step0Labels = raw9844Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9844 raw9844Labels permutation346 hz
    mixedMoment B raw9844step0 raw9844step0Labels = mixedMoment B raw9844step1 raw9844step1Labels := by
      have ha : raw9844step1 = (fun i j => raw9844step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9844step1 raw9844step0; decide +kernel
      have hl : raw9844step1Labels = raw9844step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9844step0 raw9844step0Labels permutation38 permutation2
    _ = mixedMoment B node2489 node2489Labels := by rfl

def raw9845 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -2, -1]]
def raw9845Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9845step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 0, 1], ![1, 0, -1], ![3, -2, -1]]
def raw9845step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9845step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw9845step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9845 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9845 raw9845Labels = mixedMoment B node2485 node2485Labels := by
  calc
    mixedMoment B raw9845 raw9845Labels = mixedMoment B raw9845step0 raw9845step0Labels := by
      have hz : ∀ j, raw9845 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9845step0 = (fun i j => raw9845 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9845step0 raw9845; decide +kernel
      have hl : raw9845step0Labels = raw9845Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9845 raw9845Labels permutation346 hz
    mixedMoment B raw9845step0 raw9845step0Labels = mixedMoment B raw9845step1 raw9845step1Labels := by
      have ha : raw9845step1 = (fun i j => raw9845step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9845step1 raw9845step0; decide +kernel
      have hl : raw9845step1Labels = raw9845step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9845step0 raw9845step0Labels permutation38 permutation2
    _ = mixedMoment B node2485 node2485Labels := by rfl

def raw9846 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1]]
def raw9846Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9846step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1]]
def raw9846step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9846step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9846step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9846 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9846 raw9846Labels = mixedMoment B node2723 node2723Labels := by
  calc
    mixedMoment B raw9846 raw9846Labels = mixedMoment B raw9846step0 raw9846step0Labels := by
      have hz : ∀ j, raw9846 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9846step0 = (fun i j => raw9846 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9846step0 raw9846; decide +kernel
      have hl : raw9846step0Labels = raw9846Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9846 raw9846Labels permutation346 hz
    mixedMoment B raw9846step0 raw9846step0Labels = mixedMoment B raw9846step1 raw9846step1Labels := by
      have ha : raw9846step1 = (fun i j => raw9846step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9846step1 raw9846step0; decide +kernel
      have hl : raw9846step1Labels = raw9846step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9846step0 raw9846step0Labels permutation39 permutation2
    _ = mixedMoment B node2723 node2723Labels := by rfl

def raw9847 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw9847Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9847step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw9847step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9847 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9847 raw9847Labels = mixedMoment B node5490 node5490Labels := by
  calc
    mixedMoment B raw9847 raw9847Labels = mixedMoment B raw9847step0 raw9847step0Labels := by
      have hz : ∀ j, raw9847 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9847step0 = (fun i j => raw9847 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9847step0 raw9847; decide +kernel
      have hl : raw9847step0Labels = raw9847Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9847 raw9847Labels permutation346 hz
    _ = mixedMoment B node5490 node5490Labels := by rfl

def raw9848 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9848Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9848step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9848step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9848step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw9848step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9848step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw9848step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9848 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9848 raw9848Labels = mixedMoment B node4424 node4424Labels := by
  calc
    mixedMoment B raw9848 raw9848Labels = mixedMoment B raw9848step0 raw9848step0Labels := by
      have hz : ∀ j, raw9848 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9848step0 = (fun i j => raw9848 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9848step0 raw9848; decide +kernel
      have hl : raw9848step0Labels = raw9848Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9848 raw9848Labels permutation346 hz
    mixedMoment B raw9848step0 raw9848step0Labels = mixedMoment B raw9848step1 raw9848step1Labels := by
      have ha : raw9848step1 = (fun i j => raw9848step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9848step1 raw9848step0; decide +kernel
      have hl : raw9848step1Labels = raw9848step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9848step0 raw9848step0Labels permutation40 permutation3
    mixedMoment B raw9848step1 raw9848step1Labels = mixedMoment B raw9848step2 raw9848step2Labels := by
      have ha : raw9848step2 = raw9848step1 := by apply Matrix.ext; unfold raw9848step2 raw9848step1; decide +kernel
      have hl : raw9848step1Labels = labelEmbedding6 ∘ raw9848step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9848step1 raw9848step1Labels raw9848step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4424 node4424Labels := by rfl

def raw9849 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9849Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9849step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw9849step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9849step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw9849step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9849 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9849 raw9849Labels = mixedMoment B node5059 node5059Labels := by
  calc
    mixedMoment B raw9849 raw9849Labels = mixedMoment B raw9849step0 raw9849step0Labels := by
      have ha : raw9849step0 = (fun i j => raw9849 (permutation184 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9849step0 raw9849; decide +kernel
      have hl : raw9849step0Labels = raw9849Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9849 raw9849Labels permutation184 permutation3
    mixedMoment B raw9849step0 raw9849step0Labels = mixedMoment B raw9849step1 raw9849step1Labels := by
      have ha : raw9849step1 = raw9849step0 := by apply Matrix.ext; unfold raw9849step1 raw9849step0; decide +kernel
      have hl : raw9849step0Labels = labelEmbedding6 ∘ raw9849step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9849step0 raw9849step0Labels raw9849step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5059 node5059Labels := by rfl

def raw9850 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, 0, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9850Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9850step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9850step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9850step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw9850step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9850step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw9850step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9850 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9850 raw9850Labels = mixedMoment B node5018 node5018Labels := by
  calc
    mixedMoment B raw9850 raw9850Labels = mixedMoment B raw9850step0 raw9850step0Labels := by
      have hz : ∀ j, raw9850 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9850step0 = (fun i j => raw9850 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9850step0 raw9850; decide +kernel
      have hl : raw9850step0Labels = raw9850Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9850 raw9850Labels permutation346 hz
    mixedMoment B raw9850step0 raw9850step0Labels = mixedMoment B raw9850step1 raw9850step1Labels := by
      have ha : raw9850step1 = (fun i j => raw9850step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9850step1 raw9850step0; decide +kernel
      have hl : raw9850step1Labels = raw9850step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9850step0 raw9850step0Labels permutation40 permutation3
    mixedMoment B raw9850step1 raw9850step1Labels = mixedMoment B raw9850step2 raw9850step2Labels := by
      have ha : raw9850step2 = raw9850step1 := by apply Matrix.ext; unfold raw9850step2 raw9850step1; decide +kernel
      have hl : raw9850step1Labels = labelEmbedding6 ∘ raw9850step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9850step1 raw9850step1Labels raw9850step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5018 node5018Labels := by rfl

def raw9851 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw9851Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9851step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw9851step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9851step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, 1, -1], ![2, -1, -1]]
def raw9851step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9851step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw9851step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9851step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw9851step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9851 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9851 raw9851Labels = mixedMoment B node5275 node5275Labels := by
  calc
    mixedMoment B raw9851 raw9851Labels = mixedMoment B raw9851step0 raw9851step0Labels := by
      have hz : ∀ j, raw9851 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw9851step0 = (fun i j => raw9851 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw9851step0 raw9851; decide +kernel
      have hl : raw9851step0Labels = raw9851Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9851 raw9851Labels permutation520 hz
    mixedMoment B raw9851step0 raw9851step0Labels = mixedMoment B raw9851step1 raw9851step1Labels := by
      have hz : ∀ j, raw9851step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw9851step1 = (fun i j => raw9851step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw9851step1 raw9851step0; decide +kernel
      have hl : raw9851step1Labels = raw9851step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9851step0 raw9851step0Labels permutation80 hz
    mixedMoment B raw9851step1 raw9851step1Labels = mixedMoment B raw9851step2 raw9851step2Labels := by
      have ha : raw9851step2 = (fun i j => raw9851step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9851step2 raw9851step1; decide +kernel
      have hl : raw9851step2Labels = raw9851step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9851step1 raw9851step1Labels permutation10 permutation3
    mixedMoment B raw9851step2 raw9851step2Labels = mixedMoment B raw9851step3 raw9851step3Labels := by
      have ha : raw9851step3 = raw9851step2 := by apply Matrix.ext; unfold raw9851step3 raw9851step2; decide +kernel
      have hl : raw9851step2Labels = labelEmbedding6 ∘ raw9851step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9851step2 raw9851step2Labels raw9851step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5275 node5275Labels := by rfl

def raw9852 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9852Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9852step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9852step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9852step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9852step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9852 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9852 raw9852Labels = mixedMoment B node4399 node4399Labels := by
  calc
    mixedMoment B raw9852 raw9852Labels = mixedMoment B raw9852step0 raw9852step0Labels := by
      have ha : raw9852step0 = (fun i j => raw9852 (permutation200 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9852step0 raw9852; decide +kernel
      have hl : raw9852step0Labels = raw9852Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9852 raw9852Labels permutation200 permutation3
    mixedMoment B raw9852step0 raw9852step0Labels = mixedMoment B raw9852step1 raw9852step1Labels := by
      have ha : raw9852step1 = raw9852step0 := by apply Matrix.ext; unfold raw9852step1 raw9852step0; decide +kernel
      have hl : raw9852step0Labels = labelEmbedding6 ∘ raw9852step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9852step0 raw9852step0Labels raw9852step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4399 node4399Labels := by rfl

def raw9853 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9853Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9853step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9853step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9853step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9853step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9853 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9853 raw9853Labels = mixedMoment B node5137 node5137Labels := by
  calc
    mixedMoment B raw9853 raw9853Labels = mixedMoment B raw9853step0 raw9853step0Labels := by
      have ha : raw9853step0 = (fun i j => raw9853 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9853step0 raw9853; decide +kernel
      have hl : raw9853step0Labels = raw9853Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9853 raw9853Labels permutation158 permutation3
    mixedMoment B raw9853step0 raw9853step0Labels = mixedMoment B raw9853step1 raw9853step1Labels := by
      have ha : raw9853step1 = raw9853step0 := by apply Matrix.ext; unfold raw9853step1 raw9853step0; decide +kernel
      have hl : raw9853step0Labels = labelEmbedding6 ∘ raw9853step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9853step0 raw9853step0Labels raw9853step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5137 node5137Labels := by rfl

def raw9854 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9854Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9854step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9854step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9854step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9854step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9854 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9854 raw9854Labels = mixedMoment B node4998 node4998Labels := by
  calc
    mixedMoment B raw9854 raw9854Labels = mixedMoment B raw9854step0 raw9854step0Labels := by
      have ha : raw9854step0 = (fun i j => raw9854 (permutation200 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9854step0 raw9854; decide +kernel
      have hl : raw9854step0Labels = raw9854Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9854 raw9854Labels permutation200 permutation3
    mixedMoment B raw9854step0 raw9854step0Labels = mixedMoment B raw9854step1 raw9854step1Labels := by
      have ha : raw9854step1 = raw9854step0 := by apply Matrix.ext; unfold raw9854step1 raw9854step0; decide +kernel
      have hl : raw9854step0Labels = labelEmbedding6 ∘ raw9854step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9854step0 raw9854step0Labels raw9854step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4998 node4998Labels := by rfl

def raw9855 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw9855Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9855step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw9855step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9855step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9855step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9855step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9855step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9855 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9855 raw9855Labels = mixedMoment B node5259 node5259Labels := by
  calc
    mixedMoment B raw9855 raw9855Labels = mixedMoment B raw9855step0 raw9855step0Labels := by
      have hz : ∀ j, raw9855 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw9855step0 = (fun i j => raw9855 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw9855step0 raw9855; decide +kernel
      have hl : raw9855step0Labels = raw9855Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9855 raw9855Labels permutation520 hz
    mixedMoment B raw9855step0 raw9855step0Labels = mixedMoment B raw9855step1 raw9855step1Labels := by
      have ha : raw9855step1 = (fun i j => raw9855step0 (permutation44 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9855step1 raw9855step0; decide +kernel
      have hl : raw9855step1Labels = raw9855step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9855step0 raw9855step0Labels permutation44 permutation3
    mixedMoment B raw9855step1 raw9855step1Labels = mixedMoment B raw9855step2 raw9855step2Labels := by
      have ha : raw9855step2 = raw9855step1 := by apply Matrix.ext; unfold raw9855step2 raw9855step1; decide +kernel
      have hl : raw9855step1Labels = labelEmbedding6 ∘ raw9855step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9855step1 raw9855step1Labels raw9855step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5259 node5259Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
