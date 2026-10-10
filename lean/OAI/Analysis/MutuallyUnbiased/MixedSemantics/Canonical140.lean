import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes58
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes74
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes78
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes83
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes85

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw17920 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw17920Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17920step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17920step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17920step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17920step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17920 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17920 raw17920Labels = mixedMoment B node3838 node3838Labels := by
  calc
    mixedMoment B raw17920 raw17920Labels = mixedMoment B raw17920step0 raw17920step0Labels := by
      have ha : raw17920step0 = (fun i j => raw17920 (permutation645 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17920step0 raw17920; decide +kernel
      have hl : raw17920step0Labels = raw17920Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17920 raw17920Labels permutation645 permutation7
    mixedMoment B raw17920step0 raw17920step0Labels = mixedMoment B raw17920step1 raw17920step1Labels := by
      have ha : raw17920step1 = raw17920step0 := by apply Matrix.ext; unfold raw17920step1 raw17920step0; decide +kernel
      have hl : raw17920step0Labels = labelEmbedding1 ∘ raw17920step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17920step0 raw17920step0Labels raw17920step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3838 node3838Labels := by rfl

def raw17921 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2]]
def raw17921Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17921step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2]]
def raw17921step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17921step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![2, 0, -2]]
def raw17921step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17921step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17921step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17921step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17921step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17921 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17921 raw17921Labels = mixedMoment B node3861 node3861Labels := by
  calc
    mixedMoment B raw17921 raw17921Labels = mixedMoment B raw17921step0 raw17921step0Labels := by
      have hz : ∀ j, raw17921 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw17921step0 = (fun i j => raw17921 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw17921step0 raw17921; decide +kernel
      have hl : raw17921step0Labels = raw17921Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17921 raw17921Labels permutation520 hz
    mixedMoment B raw17921step0 raw17921step0Labels = mixedMoment B raw17921step1 raw17921step1Labels := by
      have hz : ∀ j, raw17921step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw17921step1 = (fun i j => raw17921step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw17921step1 raw17921step0; decide +kernel
      have hl : raw17921step1Labels = raw17921step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17921step0 raw17921step0Labels permutation104 hz
    mixedMoment B raw17921step1 raw17921step1Labels = mixedMoment B raw17921step2 raw17921step2Labels := by
      have ha : raw17921step2 = (fun i j => raw17921step1 (permutation30 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17921step2 raw17921step1; decide +kernel
      have hl : raw17921step2Labels = raw17921step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17921step1 raw17921step1Labels permutation30 permutation7
    mixedMoment B raw17921step2 raw17921step2Labels = mixedMoment B raw17921step3 raw17921step3Labels := by
      have ha : raw17921step3 = raw17921step2 := by apply Matrix.ext; unfold raw17921step3 raw17921step2; decide +kernel
      have hl : raw17921step2Labels = labelEmbedding1 ∘ raw17921step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17921step2 raw17921step2Labels raw17921step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3861 node3861Labels := by rfl

def raw17922 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17922Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17922step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw17922step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17922step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw17922step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17922step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17922step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17922step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17922step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17922 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17922 raw17922Labels = mixedMoment B node3981 node3981Labels := by
  calc
    mixedMoment B raw17922 raw17922Labels = mixedMoment B raw17922step0 raw17922step0Labels := by
      have hz : ∀ j, raw17922 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17922step0 = (fun i j => raw17922 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17922step0 raw17922; decide +kernel
      have hl : raw17922step0Labels = raw17922Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17922 raw17922Labels permutation434 hz
    mixedMoment B raw17922step0 raw17922step0Labels = mixedMoment B raw17922step1 raw17922step1Labels := by
      have ha : raw17922step1 = (fun i j => raw17922step0 (permutation58 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17922step1 raw17922step0; decide +kernel
      have hl : raw17922step1Labels = raw17922step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17922step0 raw17922step0Labels permutation58 permutation7
    mixedMoment B raw17922step1 raw17922step1Labels = mixedMoment B raw17922step2 raw17922step2Labels := by
      have ha : raw17922step2 = -raw17922step1 := by apply Matrix.ext; change ∀ i j, raw17922step2 i j = -(raw17922step1 i j); unfold raw17922step2 raw17922step1; decide +kernel
      have hl : raw17922step2Labels = raw17922step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17922step2 raw17922step2Labels = mixedMoment B raw17922step3 raw17922step3Labels := by
      have ha : raw17922step3 = raw17922step2 := by apply Matrix.ext; unfold raw17922step3 raw17922step2; decide +kernel
      have hl : raw17922step2Labels = labelEmbedding1 ∘ raw17922step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17922step2 raw17922step2Labels raw17922step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3981 node3981Labels := by rfl

def raw17923 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw17923Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17923step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw17923step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17923step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw17923step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17923step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw17923step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17923step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw17923step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17923 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17923 raw17923Labels = mixedMoment B node3541 node3541Labels := by
  calc
    mixedMoment B raw17923 raw17923Labels = mixedMoment B raw17923step0 raw17923step0Labels := by
      have hz : ∀ j, raw17923 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17923step0 = (fun i j => raw17923 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17923step0 raw17923; decide +kernel
      have hl : raw17923step0Labels = raw17923Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17923 raw17923Labels permutation434 hz
    mixedMoment B raw17923step0 raw17923step0Labels = mixedMoment B raw17923step1 raw17923step1Labels := by
      have ha : raw17923step1 = (fun i j => raw17923step0 (permutation43 i) (permutation5 j)) := by apply Matrix.ext; unfold raw17923step1 raw17923step0; decide +kernel
      have hl : raw17923step1Labels = raw17923step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17923step0 raw17923step0Labels permutation43 permutation5
    mixedMoment B raw17923step1 raw17923step1Labels = mixedMoment B raw17923step2 raw17923step2Labels := by
      have ha : raw17923step2 = -raw17923step1 := by apply Matrix.ext; change ∀ i j, raw17923step2 i j = -(raw17923step1 i j); unfold raw17923step2 raw17923step1; decide +kernel
      have hl : raw17923step2Labels = raw17923step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17923step2 raw17923step2Labels = mixedMoment B raw17923step3 raw17923step3Labels := by
      have ha : raw17923step3 = raw17923step2 := by apply Matrix.ext; unfold raw17923step3 raw17923step2; decide +kernel
      have hl : raw17923step2Labels = labelEmbedding1 ∘ raw17923step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17923step2 raw17923step2Labels raw17923step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3541 node3541Labels := by rfl

def raw17924 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw17924Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17924step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2]]
def raw17924step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17924step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw17924step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17924step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw17924step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17924 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17924 raw17924Labels = mixedMoment B node3877 node3877Labels := by
  calc
    mixedMoment B raw17924 raw17924Labels = mixedMoment B raw17924step0 raw17924step0Labels := by
      have hz : ∀ j, raw17924 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17924step0 = (fun i j => raw17924 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17924step0 raw17924; decide +kernel
      have hl : raw17924step0Labels = raw17924Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17924 raw17924Labels permutation434 hz
    mixedMoment B raw17924step0 raw17924step0Labels = mixedMoment B raw17924step1 raw17924step1Labels := by
      have ha : raw17924step1 = (fun i j => raw17924step0 (permutation144 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17924step1 raw17924step0; decide +kernel
      have hl : raw17924step1Labels = raw17924step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17924step0 raw17924step0Labels permutation144 permutation7
    mixedMoment B raw17924step1 raw17924step1Labels = mixedMoment B raw17924step2 raw17924step2Labels := by
      have ha : raw17924step2 = raw17924step1 := by apply Matrix.ext; unfold raw17924step2 raw17924step1; decide +kernel
      have hl : raw17924step1Labels = labelEmbedding1 ∘ raw17924step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17924step1 raw17924step1Labels raw17924step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3877 node3877Labels := by rfl

def raw17925 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw17925Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17925step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17925step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17925step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17925step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17925 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17925 raw17925Labels = mixedMoment B node3839 node3839Labels := by
  calc
    mixedMoment B raw17925 raw17925Labels = mixedMoment B raw17925step0 raw17925step0Labels := by
      have ha : raw17925step0 = (fun i j => raw17925 (permutation645 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17925step0 raw17925; decide +kernel
      have hl : raw17925step0Labels = raw17925Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17925 raw17925Labels permutation645 permutation7
    mixedMoment B raw17925step0 raw17925step0Labels = mixedMoment B raw17925step1 raw17925step1Labels := by
      have ha : raw17925step1 = raw17925step0 := by apply Matrix.ext; unfold raw17925step1 raw17925step0; decide +kernel
      have hl : raw17925step0Labels = labelEmbedding1 ∘ raw17925step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17925step0 raw17925step0Labels raw17925step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3839 node3839Labels := by rfl

def raw17926 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2]]
def raw17926Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17926step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2]]
def raw17926step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17926step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 1, -1], ![2, 0, -2]]
def raw17926step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17926step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw17926step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17926step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw17926step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17926 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17926 raw17926Labels = mixedMoment B node3862 node3862Labels := by
  calc
    mixedMoment B raw17926 raw17926Labels = mixedMoment B raw17926step0 raw17926step0Labels := by
      have hz : ∀ j, raw17926 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw17926step0 = (fun i j => raw17926 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw17926step0 raw17926; decide +kernel
      have hl : raw17926step0Labels = raw17926Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17926 raw17926Labels permutation520 hz
    mixedMoment B raw17926step0 raw17926step0Labels = mixedMoment B raw17926step1 raw17926step1Labels := by
      have hz : ∀ j, raw17926step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw17926step1 = (fun i j => raw17926step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw17926step1 raw17926step0; decide +kernel
      have hl : raw17926step1Labels = raw17926step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17926step0 raw17926step0Labels permutation104 hz
    mixedMoment B raw17926step1 raw17926step1Labels = mixedMoment B raw17926step2 raw17926step2Labels := by
      have ha : raw17926step2 = (fun i j => raw17926step1 (permutation30 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17926step2 raw17926step1; decide +kernel
      have hl : raw17926step2Labels = raw17926step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17926step1 raw17926step1Labels permutation30 permutation7
    mixedMoment B raw17926step2 raw17926step2Labels = mixedMoment B raw17926step3 raw17926step3Labels := by
      have ha : raw17926step3 = raw17926step2 := by apply Matrix.ext; unfold raw17926step3 raw17926step2; decide +kernel
      have hl : raw17926step2Labels = labelEmbedding1 ∘ raw17926step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17926step2 raw17926step2Labels raw17926step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3862 node3862Labels := by rfl

def raw17927 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17927Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17927step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw17927step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17927step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw17927step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17927step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw17927step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17927 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17927 raw17927Labels = mixedMoment B node3993 node3993Labels := by
  calc
    mixedMoment B raw17927 raw17927Labels = mixedMoment B raw17927step0 raw17927step0Labels := by
      have hz : ∀ j, raw17927 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17927step0 = (fun i j => raw17927 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17927step0 raw17927; decide +kernel
      have hl : raw17927step0Labels = raw17927Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17927 raw17927Labels permutation434 hz
    mixedMoment B raw17927step0 raw17927step0Labels = mixedMoment B raw17927step1 raw17927step1Labels := by
      have ha : raw17927step1 = (fun i j => raw17927step0 (permutation144 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17927step1 raw17927step0; decide +kernel
      have hl : raw17927step1Labels = raw17927step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17927step0 raw17927step0Labels permutation144 permutation7
    mixedMoment B raw17927step1 raw17927step1Labels = mixedMoment B raw17927step2 raw17927step2Labels := by
      have ha : raw17927step2 = raw17927step1 := by apply Matrix.ext; unfold raw17927step2 raw17927step1; decide +kernel
      have hl : raw17927step1Labels = labelEmbedding1 ∘ raw17927step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17927step1 raw17927step1Labels raw17927step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3993 node3993Labels := by rfl

def raw17928 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw17928Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17928step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw17928step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17928step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1]]
def raw17928step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17928step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]
def raw17928step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17928step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]
def raw17928step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17928 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17928 raw17928Labels = mixedMoment B node3624 node3624Labels := by
  calc
    mixedMoment B raw17928 raw17928Labels = mixedMoment B raw17928step0 raw17928step0Labels := by
      have hz : ∀ j, raw17928 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17928step0 = (fun i j => raw17928 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17928step0 raw17928; decide +kernel
      have hl : raw17928step0Labels = raw17928Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17928 raw17928Labels permutation434 hz
    mixedMoment B raw17928step0 raw17928step0Labels = mixedMoment B raw17928step1 raw17928step1Labels := by
      have ha : raw17928step1 = (fun i j => raw17928step0 (permutation42 i) (permutation5 j)) := by apply Matrix.ext; unfold raw17928step1 raw17928step0; decide +kernel
      have hl : raw17928step1Labels = raw17928step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17928step0 raw17928step0Labels permutation42 permutation5
    mixedMoment B raw17928step1 raw17928step1Labels = mixedMoment B raw17928step2 raw17928step2Labels := by
      have ha : raw17928step2 = -raw17928step1 := by apply Matrix.ext; change ∀ i j, raw17928step2 i j = -(raw17928step1 i j); unfold raw17928step2 raw17928step1; decide +kernel
      have hl : raw17928step2Labels = raw17928step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17928step2 raw17928step2Labels = mixedMoment B raw17928step3 raw17928step3Labels := by
      have ha : raw17928step3 = raw17928step2 := by apply Matrix.ext; unfold raw17928step3 raw17928step2; decide +kernel
      have hl : raw17928step2Labels = labelEmbedding1 ∘ raw17928step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17928step2 raw17928step2Labels raw17928step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3624 node3624Labels := by rfl

def raw17929 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw17929Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17929step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw17929step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17929step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw17929step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17929step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw17929step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17929step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw17929step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17929 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17929 raw17929Labels = mixedMoment B node3766 node3766Labels := by
  calc
    mixedMoment B raw17929 raw17929Labels = mixedMoment B raw17929step0 raw17929step0Labels := by
      have hz : ∀ j, raw17929 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17929step0 = (fun i j => raw17929 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17929step0 raw17929; decide +kernel
      have hl : raw17929step0Labels = raw17929Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17929 raw17929Labels permutation434 hz
    mixedMoment B raw17929step0 raw17929step0Labels = mixedMoment B raw17929step1 raw17929step1Labels := by
      have ha : raw17929step1 = (fun i j => raw17929step0 (permutation58 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17929step1 raw17929step0; decide +kernel
      have hl : raw17929step1Labels = raw17929step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17929step0 raw17929step0Labels permutation58 permutation7
    mixedMoment B raw17929step1 raw17929step1Labels = mixedMoment B raw17929step2 raw17929step2Labels := by
      have ha : raw17929step2 = -raw17929step1 := by apply Matrix.ext; change ∀ i j, raw17929step2 i j = -(raw17929step1 i j); unfold raw17929step2 raw17929step1; decide +kernel
      have hl : raw17929step2Labels = raw17929step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17929step2 raw17929step2Labels = mixedMoment B raw17929step3 raw17929step3Labels := by
      have ha : raw17929step3 = raw17929step2 := by apply Matrix.ext; unfold raw17929step3 raw17929step2; decide +kernel
      have hl : raw17929step2Labels = labelEmbedding1 ∘ raw17929step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17929step2 raw17929step2Labels raw17929step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3766 node3766Labels := by rfl

def raw17930 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw17930Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17930step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17930step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17930step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17930step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17930 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17930 raw17930Labels = mixedMoment B node3794 node3794Labels := by
  calc
    mixedMoment B raw17930 raw17930Labels = mixedMoment B raw17930step0 raw17930step0Labels := by
      have ha : raw17930step0 = (fun i j => raw17930 (permutation645 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17930step0 raw17930; decide +kernel
      have hl : raw17930step0Labels = raw17930Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17930 raw17930Labels permutation645 permutation7
    mixedMoment B raw17930step0 raw17930step0Labels = mixedMoment B raw17930step1 raw17930step1Labels := by
      have ha : raw17930step1 = raw17930step0 := by apply Matrix.ext; unfold raw17930step1 raw17930step0; decide +kernel
      have hl : raw17930step0Labels = labelEmbedding1 ∘ raw17930step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17930step0 raw17930step0Labels raw17930step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3794 node3794Labels := by rfl

def raw17931 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2]]
def raw17931Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17931step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2]]
def raw17931step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17931step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![2, 0, -2]]
def raw17931step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17931step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17931step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17931step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17931step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17931 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17931 raw17931Labels = mixedMoment B node3817 node3817Labels := by
  calc
    mixedMoment B raw17931 raw17931Labels = mixedMoment B raw17931step0 raw17931step0Labels := by
      have hz : ∀ j, raw17931 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw17931step0 = (fun i j => raw17931 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw17931step0 raw17931; decide +kernel
      have hl : raw17931step0Labels = raw17931Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17931 raw17931Labels permutation520 hz
    mixedMoment B raw17931step0 raw17931step0Labels = mixedMoment B raw17931step1 raw17931step1Labels := by
      have hz : ∀ j, raw17931step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw17931step1 = (fun i j => raw17931step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw17931step1 raw17931step0; decide +kernel
      have hl : raw17931step1Labels = raw17931step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17931step0 raw17931step0Labels permutation104 hz
    mixedMoment B raw17931step1 raw17931step1Labels = mixedMoment B raw17931step2 raw17931step2Labels := by
      have ha : raw17931step2 = (fun i j => raw17931step1 (permutation30 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17931step2 raw17931step1; decide +kernel
      have hl : raw17931step2Labels = raw17931step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17931step1 raw17931step1Labels permutation30 permutation7
    mixedMoment B raw17931step2 raw17931step2Labels = mixedMoment B raw17931step3 raw17931step3Labels := by
      have ha : raw17931step3 = raw17931step2 := by apply Matrix.ext; unfold raw17931step3 raw17931step2; decide +kernel
      have hl : raw17931step2Labels = labelEmbedding1 ∘ raw17931step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17931step2 raw17931step2Labels raw17931step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3817 node3817Labels := by rfl

def raw17932 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17932Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17932step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw17932step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17932step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17932step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17932step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17932step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17932step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17932step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17932 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17932 raw17932Labels = mixedMoment B node3958 node3958Labels := by
  calc
    mixedMoment B raw17932 raw17932Labels = mixedMoment B raw17932step0 raw17932step0Labels := by
      have hz : ∀ j, raw17932 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17932step0 = (fun i j => raw17932 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17932step0 raw17932; decide +kernel
      have hl : raw17932step0Labels = raw17932Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17932 raw17932Labels permutation434 hz
    mixedMoment B raw17932step0 raw17932step0Labels = mixedMoment B raw17932step1 raw17932step1Labels := by
      have ha : raw17932step1 = (fun i j => raw17932step0 (permutation58 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17932step1 raw17932step0; decide +kernel
      have hl : raw17932step1Labels = raw17932step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17932step0 raw17932step0Labels permutation58 permutation7
    mixedMoment B raw17932step1 raw17932step1Labels = mixedMoment B raw17932step2 raw17932step2Labels := by
      have ha : raw17932step2 = -raw17932step1 := by apply Matrix.ext; change ∀ i j, raw17932step2 i j = -(raw17932step1 i j); unfold raw17932step2 raw17932step1; decide +kernel
      have hl : raw17932step2Labels = raw17932step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17932step2 raw17932step2Labels = mixedMoment B raw17932step3 raw17932step3Labels := by
      have ha : raw17932step3 = raw17932step2 := by apply Matrix.ext; unfold raw17932step3 raw17932step2; decide +kernel
      have hl : raw17932step2Labels = labelEmbedding1 ∘ raw17932step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17932step2 raw17932step2Labels raw17932step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3958 node3958Labels := by rfl

def raw17933 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw17933Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17933step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw17933step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17933step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw17933step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17933step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw17933step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17933 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17933 raw17933Labels = mixedMoment B node3537 node3537Labels := by
  calc
    mixedMoment B raw17933 raw17933Labels = mixedMoment B raw17933step0 raw17933step0Labels := by
      have ha : raw17933step0 = (fun i j => raw17933 (permutation194 i) (permutation5 j)) := by apply Matrix.ext; unfold raw17933step0 raw17933; decide +kernel
      have hl : raw17933step0Labels = raw17933Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17933 raw17933Labels permutation194 permutation5
    mixedMoment B raw17933step0 raw17933step0Labels = mixedMoment B raw17933step1 raw17933step1Labels := by
      have ha : raw17933step1 = -raw17933step0 := by apply Matrix.ext; change ∀ i j, raw17933step1 i j = -(raw17933step0 i j); unfold raw17933step1 raw17933step0; decide +kernel
      have hl : raw17933step1Labels = raw17933step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17933step1 raw17933step1Labels = mixedMoment B raw17933step2 raw17933step2Labels := by
      have ha : raw17933step2 = raw17933step1 := by apply Matrix.ext; unfold raw17933step2 raw17933step1; decide +kernel
      have hl : raw17933step1Labels = labelEmbedding1 ∘ raw17933step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17933step1 raw17933step1Labels raw17933step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3537 node3537Labels := by rfl

def raw17934 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw17934Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17934step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw17934step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17934step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw17934step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17934step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw17934step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17934 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17934 raw17934Labels = mixedMoment B node3757 node3757Labels := by
  calc
    mixedMoment B raw17934 raw17934Labels = mixedMoment B raw17934step0 raw17934step0Labels := by
      have ha : raw17934step0 = (fun i j => raw17934 (permutation273 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17934step0 raw17934; decide +kernel
      have hl : raw17934step0Labels = raw17934Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17934 raw17934Labels permutation273 permutation7
    mixedMoment B raw17934step0 raw17934step0Labels = mixedMoment B raw17934step1 raw17934step1Labels := by
      have ha : raw17934step1 = -raw17934step0 := by apply Matrix.ext; change ∀ i j, raw17934step1 i j = -(raw17934step0 i j); unfold raw17934step1 raw17934step0; decide +kernel
      have hl : raw17934step1Labels = raw17934step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17934step1 raw17934step1Labels = mixedMoment B raw17934step2 raw17934step2Labels := by
      have ha : raw17934step2 = raw17934step1 := by apply Matrix.ext; unfold raw17934step2 raw17934step1; decide +kernel
      have hl : raw17934step1Labels = labelEmbedding1 ∘ raw17934step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17934step1 raw17934step1Labels raw17934step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3757 node3757Labels := by rfl

def raw17935 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw17935Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17935step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17935step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17935step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17935step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17935 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17935 raw17935Labels = mixedMoment B node3869 node3869Labels := by
  calc
    mixedMoment B raw17935 raw17935Labels = mixedMoment B raw17935step0 raw17935step0Labels := by
      have ha : raw17935step0 = (fun i j => raw17935 (permutation639 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17935step0 raw17935; decide +kernel
      have hl : raw17935step0Labels = raw17935Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17935 raw17935Labels permutation639 permutation7
    mixedMoment B raw17935step0 raw17935step0Labels = mixedMoment B raw17935step1 raw17935step1Labels := by
      have ha : raw17935step1 = raw17935step0 := by apply Matrix.ext; unfold raw17935step1 raw17935step0; decide +kernel
      have hl : raw17935step0Labels = labelEmbedding1 ∘ raw17935step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17935step0 raw17935step0Labels raw17935step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3869 node3869Labels := by rfl

def raw17936 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw17936Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17936step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw17936step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17936step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17936step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17936step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17936step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17936 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17936 raw17936Labels = mixedMoment B node3845 node3845Labels := by
  calc
    mixedMoment B raw17936 raw17936Labels = mixedMoment B raw17936step0 raw17936step0Labels := by
      have hz : ∀ j, raw17936 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw17936step0 = (fun i j => raw17936 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw17936step0 raw17936; decide +kernel
      have hl : raw17936step0Labels = raw17936Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17936 raw17936Labels permutation520 hz
    mixedMoment B raw17936step0 raw17936step0Labels = mixedMoment B raw17936step1 raw17936step1Labels := by
      have ha : raw17936step1 = (fun i j => raw17936step0 (permutation144 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17936step1 raw17936step0; decide +kernel
      have hl : raw17936step1Labels = raw17936step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17936step0 raw17936step0Labels permutation144 permutation7
    mixedMoment B raw17936step1 raw17936step1Labels = mixedMoment B raw17936step2 raw17936step2Labels := by
      have ha : raw17936step2 = raw17936step1 := by apply Matrix.ext; unfold raw17936step2 raw17936step1; decide +kernel
      have hl : raw17936step1Labels = labelEmbedding1 ∘ raw17936step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17936step1 raw17936step1Labels raw17936step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3845 node3845Labels := by rfl

def raw17937 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17937Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17937step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw17937step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17937step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17937step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17937step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17937step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17937 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17937 raw17937Labels = mixedMoment B node3953 node3953Labels := by
  calc
    mixedMoment B raw17937 raw17937Labels = mixedMoment B raw17937step0 raw17937step0Labels := by
      have ha : raw17937step0 = (fun i j => raw17937 (permutation273 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17937step0 raw17937; decide +kernel
      have hl : raw17937step0Labels = raw17937Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17937 raw17937Labels permutation273 permutation7
    mixedMoment B raw17937step0 raw17937step0Labels = mixedMoment B raw17937step1 raw17937step1Labels := by
      have ha : raw17937step1 = -raw17937step0 := by apply Matrix.ext; change ∀ i j, raw17937step1 i j = -(raw17937step0 i j); unfold raw17937step1 raw17937step0; decide +kernel
      have hl : raw17937step1Labels = raw17937step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17937step1 raw17937step1Labels = mixedMoment B raw17937step2 raw17937step2Labels := by
      have ha : raw17937step2 = raw17937step1 := by apply Matrix.ext; unfold raw17937step2 raw17937step1; decide +kernel
      have hl : raw17937step1Labels = labelEmbedding1 ∘ raw17937step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17937step1 raw17937step1Labels raw17937step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3953 node3953Labels := by rfl

def raw17938 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw17938Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17938step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw17938step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17938step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 2, -1], ![-2, 0, 2]]
def raw17938step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17938step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw17938step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17938step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw17938step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17938 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17938 raw17938Labels = mixedMoment B node3538 node3538Labels := by
  calc
    mixedMoment B raw17938 raw17938Labels = mixedMoment B raw17938step0 raw17938step0Labels := by
      have hz : ∀ j, raw17938 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17938step0 = (fun i j => raw17938 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17938step0 raw17938; decide +kernel
      have hl : raw17938step0Labels = raw17938Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17938 raw17938Labels permutation434 hz
    mixedMoment B raw17938step0 raw17938step0Labels = mixedMoment B raw17938step1 raw17938step1Labels := by
      have ha : raw17938step1 = (fun i j => raw17938step0 (permutation42 i) (permutation5 j)) := by apply Matrix.ext; unfold raw17938step1 raw17938step0; decide +kernel
      have hl : raw17938step1Labels = raw17938step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17938step0 raw17938step0Labels permutation42 permutation5
    mixedMoment B raw17938step1 raw17938step1Labels = mixedMoment B raw17938step2 raw17938step2Labels := by
      have ha : raw17938step2 = -raw17938step1 := by apply Matrix.ext; change ∀ i j, raw17938step2 i j = -(raw17938step1 i j); unfold raw17938step2 raw17938step1; decide +kernel
      have hl : raw17938step2Labels = raw17938step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17938step2 raw17938step2Labels = mixedMoment B raw17938step3 raw17938step3Labels := by
      have ha : raw17938step3 = raw17938step2 := by apply Matrix.ext; unfold raw17938step3 raw17938step2; decide +kernel
      have hl : raw17938step2Labels = labelEmbedding1 ∘ raw17938step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17938step2 raw17938step2Labels raw17938step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3538 node3538Labels := by rfl

def raw17939 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw17939Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17939step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw17939step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17939step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw17939step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17939step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw17939step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17939step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw17939step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17939 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17939 raw17939Labels = mixedMoment B node3770 node3770Labels := by
  calc
    mixedMoment B raw17939 raw17939Labels = mixedMoment B raw17939step0 raw17939step0Labels := by
      have hz : ∀ j, raw17939 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17939step0 = (fun i j => raw17939 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17939step0 raw17939; decide +kernel
      have hl : raw17939step0Labels = raw17939Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17939 raw17939Labels permutation434 hz
    mixedMoment B raw17939step0 raw17939step0Labels = mixedMoment B raw17939step1 raw17939step1Labels := by
      have ha : raw17939step1 = (fun i j => raw17939step0 (permutation58 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17939step1 raw17939step0; decide +kernel
      have hl : raw17939step1Labels = raw17939step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17939step0 raw17939step0Labels permutation58 permutation7
    mixedMoment B raw17939step1 raw17939step1Labels = mixedMoment B raw17939step2 raw17939step2Labels := by
      have ha : raw17939step2 = -raw17939step1 := by apply Matrix.ext; change ∀ i j, raw17939step2 i j = -(raw17939step1 i j); unfold raw17939step2 raw17939step1; decide +kernel
      have hl : raw17939step2Labels = raw17939step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17939step2 raw17939step2Labels = mixedMoment B raw17939step3 raw17939step3Labels := by
      have ha : raw17939step3 = raw17939step2 := by apply Matrix.ext; unfold raw17939step3 raw17939step2; decide +kernel
      have hl : raw17939step2Labels = labelEmbedding1 ∘ raw17939step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17939step2 raw17939step2Labels raw17939step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3770 node3770Labels := by rfl

def raw17940 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw17940Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17940step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw17940step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17940step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw17940step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17940step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw17940step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17940 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17940 raw17940Labels = mixedMoment B node3868 node3868Labels := by
  calc
    mixedMoment B raw17940 raw17940Labels = mixedMoment B raw17940step0 raw17940step0Labels := by
      have hz : ∀ j, raw17940 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17940step0 = (fun i j => raw17940 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17940step0 raw17940; decide +kernel
      have hl : raw17940step0Labels = raw17940Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17940 raw17940Labels permutation434 hz
    mixedMoment B raw17940step0 raw17940step0Labels = mixedMoment B raw17940step1 raw17940step1Labels := by
      have ha : raw17940step1 = (fun i j => raw17940step0 (permutation114 i) (permutation5 j)) := by apply Matrix.ext; unfold raw17940step1 raw17940step0; decide +kernel
      have hl : raw17940step1Labels = raw17940step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17940step0 raw17940step0Labels permutation114 permutation5
    mixedMoment B raw17940step1 raw17940step1Labels = mixedMoment B raw17940step2 raw17940step2Labels := by
      have ha : raw17940step2 = raw17940step1 := by apply Matrix.ext; unfold raw17940step2 raw17940step1; decide +kernel
      have hl : raw17940step1Labels = labelEmbedding1 ∘ raw17940step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17940step1 raw17940step1Labels raw17940step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3868 node3868Labels := by rfl

def raw17941 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw17941Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17941step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17941step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17941step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17941step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17941 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17941 raw17941Labels = mixedMoment B node3832 node3832Labels := by
  calc
    mixedMoment B raw17941 raw17941Labels = mixedMoment B raw17941step0 raw17941step0Labels := by
      have ha : raw17941step0 = (fun i j => raw17941 (permutation645 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17941step0 raw17941; decide +kernel
      have hl : raw17941step0Labels = raw17941Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17941 raw17941Labels permutation645 permutation7
    mixedMoment B raw17941step0 raw17941step0Labels = mixedMoment B raw17941step1 raw17941step1Labels := by
      have ha : raw17941step1 = raw17941step0 := by apply Matrix.ext; unfold raw17941step1 raw17941step0; decide +kernel
      have hl : raw17941step0Labels = labelEmbedding1 ∘ raw17941step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17941step0 raw17941step0Labels raw17941step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3832 node3832Labels := by rfl

def raw17942 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw17942Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17942step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![2, -2, 0], ![1, 1, -2]]
def raw17942step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17942step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw17942step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17942step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw17942step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17942 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17942 raw17942Labels = mixedMoment B node3884 node3884Labels := by
  calc
    mixedMoment B raw17942 raw17942Labels = mixedMoment B raw17942step0 raw17942step0Labels := by
      have hz : ∀ j, raw17942 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17942step0 = (fun i j => raw17942 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17942step0 raw17942; decide +kernel
      have hl : raw17942step0Labels = raw17942Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17942 raw17942Labels permutation434 hz
    mixedMoment B raw17942step0 raw17942step0Labels = mixedMoment B raw17942step1 raw17942step1Labels := by
      have ha : raw17942step1 = (fun i j => raw17942step0 (permutation115 i) (permutation5 j)) := by apply Matrix.ext; unfold raw17942step1 raw17942step0; decide +kernel
      have hl : raw17942step1Labels = raw17942step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17942step0 raw17942step0Labels permutation115 permutation5
    mixedMoment B raw17942step1 raw17942step1Labels = mixedMoment B raw17942step2 raw17942step2Labels := by
      have ha : raw17942step2 = raw17942step1 := by apply Matrix.ext; unfold raw17942step2 raw17942step1; decide +kernel
      have hl : raw17942step1Labels = labelEmbedding1 ∘ raw17942step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17942step1 raw17942step1Labels raw17942step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3884 node3884Labels := by rfl

def raw17943 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw17943Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17943step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw17943step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17943step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw17943step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17943step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw17943step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17943 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17943 raw17943Labels = mixedMoment B node3523 node3523Labels := by
  calc
    mixedMoment B raw17943 raw17943Labels = mixedMoment B raw17943step0 raw17943step0Labels := by
      have hz : ∀ j, raw17943 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17943step0 = (fun i j => raw17943 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17943step0 raw17943; decide +kernel
      have hl : raw17943step0Labels = raw17943Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17943 raw17943Labels permutation434 hz
    mixedMoment B raw17943step0 raw17943step0Labels = mixedMoment B raw17943step1 raw17943step1Labels := by
      have ha : raw17943step1 = (fun i j => raw17943step0 (permutation144 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17943step1 raw17943step0; decide +kernel
      have hl : raw17943step1Labels = raw17943step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17943step0 raw17943step0Labels permutation144 permutation7
    mixedMoment B raw17943step1 raw17943step1Labels = mixedMoment B raw17943step2 raw17943step2Labels := by
      have ha : raw17943step2 = raw17943step1 := by apply Matrix.ext; unfold raw17943step2 raw17943step1; decide +kernel
      have hl : raw17943step1Labels = labelEmbedding1 ∘ raw17943step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17943step1 raw17943step1Labels raw17943step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3523 node3523Labels := by rfl

def raw17944 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw17944Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17944step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw17944step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17944step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw17944step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17944step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw17944step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17944 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17944 raw17944Labels = mixedMoment B node3522 node3522Labels := by
  calc
    mixedMoment B raw17944 raw17944Labels = mixedMoment B raw17944step0 raw17944step0Labels := by
      have hz : ∀ j, raw17944 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17944step0 = (fun i j => raw17944 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17944step0 raw17944; decide +kernel
      have hl : raw17944step0Labels = raw17944Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17944 raw17944Labels permutation434 hz
    mixedMoment B raw17944step0 raw17944step0Labels = mixedMoment B raw17944step1 raw17944step1Labels := by
      have ha : raw17944step1 = (fun i j => raw17944step0 (permutation144 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17944step1 raw17944step0; decide +kernel
      have hl : raw17944step1Labels = raw17944step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17944step0 raw17944step0Labels permutation144 permutation7
    mixedMoment B raw17944step1 raw17944step1Labels = mixedMoment B raw17944step2 raw17944step2Labels := by
      have ha : raw17944step2 = raw17944step1 := by apply Matrix.ext; unfold raw17944step2 raw17944step1; decide +kernel
      have hl : raw17944step1Labels = labelEmbedding1 ∘ raw17944step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17944step1 raw17944step1Labels raw17944step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3522 node3522Labels := by rfl

def raw17945 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw17945Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17945step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![1, -1, 0], ![3, -1, -2]]
def raw17945step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17945step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17945step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17945step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17945step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17945 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17945 raw17945Labels = mixedMoment B node3565 node3565Labels := by
  calc
    mixedMoment B raw17945 raw17945Labels = mixedMoment B raw17945step0 raw17945step0Labels := by
      have hz : ∀ j, raw17945 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17945step0 = (fun i j => raw17945 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17945step0 raw17945; decide +kernel
      have hl : raw17945step0Labels = raw17945Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17945 raw17945Labels permutation434 hz
    mixedMoment B raw17945step0 raw17945step0Labels = mixedMoment B raw17945step1 raw17945step1Labels := by
      have ha : raw17945step1 = (fun i j => raw17945step0 (permutation144 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17945step1 raw17945step0; decide +kernel
      have hl : raw17945step1Labels = raw17945step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17945step0 raw17945step0Labels permutation144 permutation7
    mixedMoment B raw17945step1 raw17945step1Labels = mixedMoment B raw17945step2 raw17945step2Labels := by
      have ha : raw17945step2 = raw17945step1 := by apply Matrix.ext; unfold raw17945step2 raw17945step1; decide +kernel
      have hl : raw17945step1Labels = labelEmbedding1 ∘ raw17945step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17945step1 raw17945step1Labels raw17945step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3565 node3565Labels := by rfl

def raw17946 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw17946Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17946step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17946step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17946step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17946step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17946 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17946 raw17946Labels = mixedMoment B node3515 node3515Labels := by
  calc
    mixedMoment B raw17946 raw17946Labels = mixedMoment B raw17946step0 raw17946step0Labels := by
      have ha : raw17946step0 = (fun i j => raw17946 (permutation645 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17946step0 raw17946; decide +kernel
      have hl : raw17946step0Labels = raw17946Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17946 raw17946Labels permutation645 permutation7
    mixedMoment B raw17946step0 raw17946step0Labels = mixedMoment B raw17946step1 raw17946step1Labels := by
      have ha : raw17946step1 = raw17946step0 := by apply Matrix.ext; unfold raw17946step1 raw17946step0; decide +kernel
      have hl : raw17946step0Labels = labelEmbedding1 ∘ raw17946step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17946step0 raw17946step0Labels raw17946step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3515 node3515Labels := by rfl

def raw17947 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw17947Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17947step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![3, -1, -2]]
def raw17947step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17947step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![3, -1, -2]]
def raw17947step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17947step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17947step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17947step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17947step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17947 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17947 raw17947Labels = mixedMoment B node3548 node3548Labels := by
  calc
    mixedMoment B raw17947 raw17947Labels = mixedMoment B raw17947step0 raw17947step0Labels := by
      have hz : ∀ j, raw17947 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw17947step0 = (fun i j => raw17947 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw17947step0 raw17947; decide +kernel
      have hl : raw17947step0Labels = raw17947Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17947 raw17947Labels permutation520 hz
    mixedMoment B raw17947step0 raw17947step0Labels = mixedMoment B raw17947step1 raw17947step1Labels := by
      have hz : ∀ j, raw17947step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw17947step1 = (fun i j => raw17947step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw17947step1 raw17947step0; decide +kernel
      have hl : raw17947step1Labels = raw17947step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17947step0 raw17947step0Labels permutation104 hz
    mixedMoment B raw17947step1 raw17947step1Labels = mixedMoment B raw17947step2 raw17947step2Labels := by
      have ha : raw17947step2 = (fun i j => raw17947step1 (permutation30 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17947step2 raw17947step1; decide +kernel
      have hl : raw17947step2Labels = raw17947step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17947step1 raw17947step1Labels permutation30 permutation7
    mixedMoment B raw17947step2 raw17947step2Labels = mixedMoment B raw17947step3 raw17947step3Labels := by
      have ha : raw17947step3 = raw17947step2 := by apply Matrix.ext; unfold raw17947step3 raw17947step2; decide +kernel
      have hl : raw17947step2Labels = labelEmbedding1 ∘ raw17947step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17947step2 raw17947step2Labels raw17947step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3548 node3548Labels := by rfl

def raw17948 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 3, -1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw17948Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17948step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 3, -1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw17948step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17948step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw17948step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17948step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw17948step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17948step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw17948step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17948 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17948 raw17948Labels = mixedMoment B node5258 node5258Labels := by
  calc
    mixedMoment B raw17948 raw17948Labels = mixedMoment B raw17948step0 raw17948step0Labels := by
      have hz : ∀ j, raw17948 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17948step0 = (fun i j => raw17948 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17948step0 raw17948; decide +kernel
      have hl : raw17948step0Labels = raw17948Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17948 raw17948Labels permutation434 hz
    mixedMoment B raw17948step0 raw17948step0Labels = mixedMoment B raw17948step1 raw17948step1Labels := by
      have ha : raw17948step1 = (fun i j => raw17948step0 (permutation58 i) (permutation5 j)) := by apply Matrix.ext; unfold raw17948step1 raw17948step0; decide +kernel
      have hl : raw17948step1Labels = raw17948step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17948step0 raw17948step0Labels permutation58 permutation5
    mixedMoment B raw17948step1 raw17948step1Labels = mixedMoment B raw17948step2 raw17948step2Labels := by
      have ha : raw17948step2 = -raw17948step1 := by apply Matrix.ext; change ∀ i j, raw17948step2 i j = -(raw17948step1 i j); unfold raw17948step2 raw17948step1; decide +kernel
      have hl : raw17948step2Labels = raw17948step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17948step2 raw17948step2Labels = mixedMoment B raw17948step3 raw17948step3Labels := by
      have ha : raw17948step3 = raw17948step2 := by apply Matrix.ext; unfold raw17948step3 raw17948step2; decide +kernel
      have hl : raw17948step2Labels = labelEmbedding8 ∘ raw17948step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17948step2 raw17948step2Labels raw17948step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5258 node5258Labels := by rfl

def raw17949 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 2, -1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw17949Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17949step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 2, -1], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0]]
def raw17949step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17949step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw17949step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17949step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17949step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17949step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17949step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17949 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17949 raw17949Labels = mixedMoment B node5439 node5439Labels := by
  calc
    mixedMoment B raw17949 raw17949Labels = mixedMoment B raw17949step0 raw17949step0Labels := by
      have hz : ∀ j, raw17949 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17949step0 = (fun i j => raw17949 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17949step0 raw17949; decide +kernel
      have hl : raw17949step0Labels = raw17949Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17949 raw17949Labels permutation434 hz
    mixedMoment B raw17949step0 raw17949step0Labels = mixedMoment B raw17949step1 raw17949step1Labels := by
      have ha : raw17949step1 = (fun i j => raw17949step0 (permutation147 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17949step1 raw17949step0; decide +kernel
      have hl : raw17949step1Labels = raw17949step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17949step0 raw17949step0Labels permutation147 permutation3
    mixedMoment B raw17949step1 raw17949step1Labels = mixedMoment B raw17949step2 raw17949step2Labels := by
      have ha : raw17949step2 = -raw17949step1 := by apply Matrix.ext; change ∀ i j, raw17949step2 i j = -(raw17949step1 i j); unfold raw17949step2 raw17949step1; decide +kernel
      have hl : raw17949step2Labels = raw17949step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17949step2 raw17949step2Labels = mixedMoment B raw17949step3 raw17949step3Labels := by
      have ha : raw17949step3 = raw17949step2 := by apply Matrix.ext; unfold raw17949step3 raw17949step2; decide +kernel
      have hl : raw17949step2Labels = labelEmbedding6 ∘ raw17949step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17949step2 raw17949step2Labels raw17949step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5439 node5439Labels := by rfl

def raw17950 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 2, -1], ![0, -1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw17950Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17950step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17950step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17950step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17950step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17950 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17950 raw17950Labels = mixedMoment B node5424 node5424Labels := by
  calc
    mixedMoment B raw17950 raw17950Labels = mixedMoment B raw17950step0 raw17950step0Labels := by
      have ha : raw17950step0 = (fun i j => raw17950 (permutation642 i) (permutation5 j)) := by apply Matrix.ext; unfold raw17950step0 raw17950; decide +kernel
      have hl : raw17950step0Labels = raw17950Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17950 raw17950Labels permutation642 permutation5
    mixedMoment B raw17950step0 raw17950step0Labels = mixedMoment B raw17950step1 raw17950step1Labels := by
      have ha : raw17950step1 = raw17950step0 := by apply Matrix.ext; unfold raw17950step1 raw17950step0; decide +kernel
      have hl : raw17950step0Labels = labelEmbedding8 ∘ raw17950step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17950step0 raw17950step0Labels raw17950step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5424 node5424Labels := by rfl

def raw17951 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 2, -1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0]]
def raw17951Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17951step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0]]
def raw17951step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17951step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17951step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17951step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17951step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17951 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17951 raw17951Labels = mixedMoment B node5434 node5434Labels := by
  calc
    mixedMoment B raw17951 raw17951Labels = mixedMoment B raw17951step0 raw17951step0Labels := by
      have hz : ∀ j, raw17951 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17951step0 = (fun i j => raw17951 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17951step0 raw17951; decide +kernel
      have hl : raw17951step0Labels = raw17951Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17951 raw17951Labels permutation434 hz
    mixedMoment B raw17951step0 raw17951step0Labels = mixedMoment B raw17951step1 raw17951step1Labels := by
      have ha : raw17951step1 = (fun i j => raw17951step0 (permutation141 i) (permutation5 j)) := by apply Matrix.ext; unfold raw17951step1 raw17951step0; decide +kernel
      have hl : raw17951step1Labels = raw17951step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17951step0 raw17951step0Labels permutation141 permutation5
    mixedMoment B raw17951step1 raw17951step1Labels = mixedMoment B raw17951step2 raw17951step2Labels := by
      have ha : raw17951step2 = raw17951step1 := by apply Matrix.ext; unfold raw17951step2 raw17951step1; decide +kernel
      have hl : raw17951step1Labels = labelEmbedding8 ∘ raw17951step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17951step1 raw17951step1Labels raw17951step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5434 node5434Labels := by rfl

def raw17952 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 2, -1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0]]
def raw17952Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17952step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0]]
def raw17952step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17952step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw17952step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17952step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw17952step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17952step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw17952step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17952 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17952 raw17952Labels = mixedMoment B node5490 node5490Labels := by
  calc
    mixedMoment B raw17952 raw17952Labels = mixedMoment B raw17952step0 raw17952step0Labels := by
      have hz : ∀ j, raw17952 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17952step0 = (fun i j => raw17952 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17952step0 raw17952; decide +kernel
      have hl : raw17952step0Labels = raw17952Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17952 raw17952Labels permutation434 hz
    mixedMoment B raw17952step0 raw17952step0Labels = mixedMoment B raw17952step1 raw17952step1Labels := by
      have ha : raw17952step1 = (fun i j => raw17952step0 (permutation69 i) (permutation4 j)) := by apply Matrix.ext; unfold raw17952step1 raw17952step0; decide +kernel
      have hl : raw17952step1Labels = raw17952step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17952step0 raw17952step0Labels permutation69 permutation4
    mixedMoment B raw17952step1 raw17952step1Labels = mixedMoment B raw17952step2 raw17952step2Labels := by
      have ha : raw17952step2 = -raw17952step1 := by apply Matrix.ext; change ∀ i j, raw17952step2 i j = -(raw17952step1 i j); unfold raw17952step2 raw17952step1; decide +kernel
      have hl : raw17952step2Labels = raw17952step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17952step2 raw17952step2Labels = mixedMoment B raw17952step3 raw17952step3Labels := by
      have ha : raw17952step3 = raw17952step2 := by apply Matrix.ext; unfold raw17952step3 raw17952step2; decide +kernel
      have hl : raw17952step2Labels = labelEmbedding7 ∘ raw17952step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17952step2 raw17952step2Labels raw17952step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5490 node5490Labels := by rfl

def raw17953 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw17953Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17953step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw17953step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17953step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw17953step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17953step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw17953step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17953 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17953 raw17953Labels = mixedMoment B node5258 node5258Labels := by
  calc
    mixedMoment B raw17953 raw17953Labels = mixedMoment B raw17953step0 raw17953step0Labels := by
      have hz : ∀ j, raw17953 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17953step0 = (fun i j => raw17953 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17953step0 raw17953; decide +kernel
      have hl : raw17953step0Labels = raw17953Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17953 raw17953Labels permutation434 hz
    mixedMoment B raw17953step0 raw17953step0Labels = mixedMoment B raw17953step1 raw17953step1Labels := by
      have ha : raw17953step1 = (fun i j => raw17953step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17953step1 raw17953step0; decide +kernel
      have hl : raw17953step1Labels = raw17953step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17953step0 raw17953step0Labels permutation32 permutation3
    mixedMoment B raw17953step1 raw17953step1Labels = mixedMoment B raw17953step2 raw17953step2Labels := by
      have ha : raw17953step2 = raw17953step1 := by apply Matrix.ext; unfold raw17953step2 raw17953step1; decide +kernel
      have hl : raw17953step1Labels = labelEmbedding6 ∘ raw17953step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17953step1 raw17953step1Labels raw17953step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5258 node5258Labels := by rfl

def raw17954 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw17954Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17954step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0]]
def raw17954step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17954step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw17954step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17954step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17954step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17954step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17954step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17954 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17954 raw17954Labels = mixedMoment B node5434 node5434Labels := by
  calc
    mixedMoment B raw17954 raw17954Labels = mixedMoment B raw17954step0 raw17954step0Labels := by
      have hz : ∀ j, raw17954 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17954step0 = (fun i j => raw17954 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17954step0 raw17954; decide +kernel
      have hl : raw17954step0Labels = raw17954Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17954 raw17954Labels permutation434 hz
    mixedMoment B raw17954step0 raw17954step0Labels = mixedMoment B raw17954step1 raw17954step1Labels := by
      have ha : raw17954step1 = (fun i j => raw17954step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17954step1 raw17954step0; decide +kernel
      have hl : raw17954step1Labels = raw17954step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17954step0 raw17954step0Labels permutation149 permutation3
    mixedMoment B raw17954step1 raw17954step1Labels = mixedMoment B raw17954step2 raw17954step2Labels := by
      have ha : raw17954step2 = -raw17954step1 := by apply Matrix.ext; change ∀ i j, raw17954step2 i j = -(raw17954step1 i j); unfold raw17954step2 raw17954step1; decide +kernel
      have hl : raw17954step2Labels = raw17954step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17954step2 raw17954step2Labels = mixedMoment B raw17954step3 raw17954step3Labels := by
      have ha : raw17954step3 = raw17954step2 := by apply Matrix.ext; unfold raw17954step3 raw17954step2; decide +kernel
      have hl : raw17954step2Labels = labelEmbedding6 ∘ raw17954step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17954step2 raw17954step2Labels raw17954step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5434 node5434Labels := by rfl

def raw17955 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw17955Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17955step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17955step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17955step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17955step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17955step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17955step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17955 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17955 raw17955Labels = mixedMoment B node5424 node5424Labels := by
  calc
    mixedMoment B raw17955 raw17955Labels = mixedMoment B raw17955step0 raw17955step0Labels := by
      have ha : raw17955step0 = (fun i j => raw17955 (permutation680 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17955step0 raw17955; decide +kernel
      have hl : raw17955step0Labels = raw17955Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17955 raw17955Labels permutation680 permutation3
    mixedMoment B raw17955step0 raw17955step0Labels = mixedMoment B raw17955step1 raw17955step1Labels := by
      have ha : raw17955step1 = -raw17955step0 := by apply Matrix.ext; change ∀ i j, raw17955step1 i j = -(raw17955step0 i j); unfold raw17955step1 raw17955step0; decide +kernel
      have hl : raw17955step1Labels = raw17955step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17955step1 raw17955step1Labels = mixedMoment B raw17955step2 raw17955step2Labels := by
      have ha : raw17955step2 = raw17955step1 := by apply Matrix.ext; unfold raw17955step2 raw17955step1; decide +kernel
      have hl : raw17955step1Labels = labelEmbedding6 ∘ raw17955step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17955step1 raw17955step1Labels raw17955step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5424 node5424Labels := by rfl

def raw17956 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0]]
def raw17956Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17956step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0]]
def raw17956step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17956step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17956step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17956step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17956step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17956 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17956 raw17956Labels = mixedMoment B node5439 node5439Labels := by
  calc
    mixedMoment B raw17956 raw17956Labels = mixedMoment B raw17956step0 raw17956step0Labels := by
      have hz : ∀ j, raw17956 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17956step0 = (fun i j => raw17956 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17956step0 raw17956; decide +kernel
      have hl : raw17956step0Labels = raw17956Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17956 raw17956Labels permutation434 hz
    mixedMoment B raw17956step0 raw17956step0Labels = mixedMoment B raw17956step1 raw17956step1Labels := by
      have ha : raw17956step1 = (fun i j => raw17956step0 (permutation143 i) (permutation5 j)) := by apply Matrix.ext; unfold raw17956step1 raw17956step0; decide +kernel
      have hl : raw17956step1Labels = raw17956step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17956step0 raw17956step0Labels permutation143 permutation5
    mixedMoment B raw17956step1 raw17956step1Labels = mixedMoment B raw17956step2 raw17956step2Labels := by
      have ha : raw17956step2 = raw17956step1 := by apply Matrix.ext; unfold raw17956step2 raw17956step1; decide +kernel
      have hl : raw17956step1Labels = labelEmbedding8 ∘ raw17956step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17956step1 raw17956step1Labels raw17956step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5439 node5439Labels := by rfl

def raw17957 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0]]
def raw17957Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17957step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0]]
def raw17957step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17957step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw17957step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17957 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17957 raw17957Labels = mixedMoment B node5490 node5490Labels := by
  calc
    mixedMoment B raw17957 raw17957Labels = mixedMoment B raw17957step0 raw17957step0Labels := by
      have hz : ∀ j, raw17957 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17957step0 = (fun i j => raw17957 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17957step0 raw17957; decide +kernel
      have hl : raw17957step0Labels = raw17957Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17957 raw17957Labels permutation434 hz
    mixedMoment B raw17957step0 raw17957step0Labels = mixedMoment B raw17957step1 raw17957step1Labels := by
      have ha : raw17957step1 = (fun i j => raw17957step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17957step1 raw17957step0; decide +kernel
      have hl : raw17957step1Labels = raw17957step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17957step0 raw17957step0Labels permutation39 permutation2
    _ = mixedMoment B node5490 node5490Labels := by rfl

def raw17958 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![1, -2, 1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw17958Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17958step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -2, 0]]
def raw17958step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17958step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw17958step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17958step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw17958step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17958 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17958 raw17958Labels = mixedMoment B node5015 node5015Labels := by
  calc
    mixedMoment B raw17958 raw17958Labels = mixedMoment B raw17958step0 raw17958step0Labels := by
      have hz : ∀ j, raw17958 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17958step0 = (fun i j => raw17958 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17958step0 raw17958; decide +kernel
      have hl : raw17958step0Labels = raw17958Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17958 raw17958Labels permutation434 hz
    mixedMoment B raw17958step0 raw17958step0Labels = mixedMoment B raw17958step1 raw17958step1Labels := by
      have ha : raw17958step1 = (fun i j => raw17958step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17958step1 raw17958step0; decide +kernel
      have hl : raw17958step1Labels = raw17958step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17958step0 raw17958step0Labels permutation34 permutation3
    mixedMoment B raw17958step1 raw17958step1Labels = mixedMoment B raw17958step2 raw17958step2Labels := by
      have ha : raw17958step2 = raw17958step1 := by apply Matrix.ext; unfold raw17958step2 raw17958step1; decide +kernel
      have hl : raw17958step1Labels = labelEmbedding6 ∘ raw17958step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17958step1 raw17958step1Labels raw17958step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5015 node5015Labels := by rfl

def raw17959 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 3, -1], ![1, -2, 1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw17959Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17959step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 3, -1], ![1, -2, 1], ![1, 0, -1], ![2, -2, 0]]
def raw17959step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17959step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![0, -1, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw17959step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17959step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw17959step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17959step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw17959step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17959 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17959 raw17959Labels = mixedMoment B node5003 node5003Labels := by
  calc
    mixedMoment B raw17959 raw17959Labels = mixedMoment B raw17959step0 raw17959step0Labels := by
      have hz : ∀ j, raw17959 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17959step0 = (fun i j => raw17959 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17959step0 raw17959; decide +kernel
      have hl : raw17959step0Labels = raw17959Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17959 raw17959Labels permutation434 hz
    mixedMoment B raw17959step0 raw17959step0Labels = mixedMoment B raw17959step1 raw17959step1Labels := by
      have ha : raw17959step1 = (fun i j => raw17959step0 (permutation58 i) (permutation5 j)) := by apply Matrix.ext; unfold raw17959step1 raw17959step0; decide +kernel
      have hl : raw17959step1Labels = raw17959step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17959step0 raw17959step0Labels permutation58 permutation5
    mixedMoment B raw17959step1 raw17959step1Labels = mixedMoment B raw17959step2 raw17959step2Labels := by
      have ha : raw17959step2 = -raw17959step1 := by apply Matrix.ext; change ∀ i j, raw17959step2 i j = -(raw17959step1 i j); unfold raw17959step2 raw17959step1; decide +kernel
      have hl : raw17959step2Labels = raw17959step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17959step2 raw17959step2Labels = mixedMoment B raw17959step3 raw17959step3Labels := by
      have ha : raw17959step3 = raw17959step2 := by apply Matrix.ext; unfold raw17959step3 raw17959step2; decide +kernel
      have hl : raw17959step2Labels = labelEmbedding8 ∘ raw17959step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17959step2 raw17959step2Labels raw17959step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5003 node5003Labels := by rfl

def raw17960 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, -2, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw17960Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17960step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17960step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17960step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17960step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17960 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17960 raw17960Labels = mixedMoment B node5346 node5346Labels := by
  calc
    mixedMoment B raw17960 raw17960Labels = mixedMoment B raw17960step0 raw17960step0Labels := by
      have ha : raw17960step0 = (fun i j => raw17960 (permutation645 i) (permutation5 j)) := by apply Matrix.ext; unfold raw17960step0 raw17960; decide +kernel
      have hl : raw17960step0Labels = raw17960Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17960 raw17960Labels permutation645 permutation5
    mixedMoment B raw17960step0 raw17960step0Labels = mixedMoment B raw17960step1 raw17960step1Labels := by
      have ha : raw17960step1 = raw17960step0 := by apply Matrix.ext; unfold raw17960step1 raw17960step0; decide +kernel
      have hl : raw17960step0Labels = labelEmbedding8 ∘ raw17960step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17960step0 raw17960step0Labels raw17960step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5346 node5346Labels := by rfl

def raw17961 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, -2, 1], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0]]
def raw17961Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17961step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, -2, 1], ![0, 1, -1], ![2, -2, 0]]
def raw17961step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17961step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17961step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17961step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17961step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17961 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17961 raw17961Labels = mixedMoment B node5368 node5368Labels := by
  calc
    mixedMoment B raw17961 raw17961Labels = mixedMoment B raw17961step0 raw17961step0Labels := by
      have hz : ∀ j, raw17961 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17961step0 = (fun i j => raw17961 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17961step0 raw17961; decide +kernel
      have hl : raw17961step0Labels = raw17961Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17961 raw17961Labels permutation434 hz
    mixedMoment B raw17961step0 raw17961step0Labels = mixedMoment B raw17961step1 raw17961step1Labels := by
      have ha : raw17961step1 = (fun i j => raw17961step0 (permutation144 i) (permutation5 j)) := by apply Matrix.ext; unfold raw17961step1 raw17961step0; decide +kernel
      have hl : raw17961step1Labels = raw17961step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17961step0 raw17961step0Labels permutation144 permutation5
    mixedMoment B raw17961step1 raw17961step1Labels = mixedMoment B raw17961step2 raw17961step2Labels := by
      have ha : raw17961step2 = raw17961step1 := by apply Matrix.ext; unfold raw17961step2 raw17961step1; decide +kernel
      have hl : raw17961step1Labels = labelEmbedding8 ∘ raw17961step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17961step1 raw17961step1Labels raw17961step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5368 node5368Labels := by rfl

def raw17962 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, -2, 1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0]]
def raw17962Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17962step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, -1, 0]]
def raw17962step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17962step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17962step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17962step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17962step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17962step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17962step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17962 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17962 raw17962Labels = mixedMoment B node5473 node5473Labels := by
  calc
    mixedMoment B raw17962 raw17962Labels = mixedMoment B raw17962step0 raw17962step0Labels := by
      have hz : ∀ j, raw17962 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17962step0 = (fun i j => raw17962 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17962step0 raw17962; decide +kernel
      have hl : raw17962step0Labels = raw17962Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17962 raw17962Labels permutation434 hz
    mixedMoment B raw17962step0 raw17962step0Labels = mixedMoment B raw17962step1 raw17962step1Labels := by
      have ha : raw17962step1 = (fun i j => raw17962step0 (permutation59 i) (permutation5 j)) := by apply Matrix.ext; unfold raw17962step1 raw17962step0; decide +kernel
      have hl : raw17962step1Labels = raw17962step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17962step0 raw17962step0Labels permutation59 permutation5
    mixedMoment B raw17962step1 raw17962step1Labels = mixedMoment B raw17962step2 raw17962step2Labels := by
      have ha : raw17962step2 = -raw17962step1 := by apply Matrix.ext; change ∀ i j, raw17962step2 i j = -(raw17962step1 i j); unfold raw17962step2 raw17962step1; decide +kernel
      have hl : raw17962step2Labels = raw17962step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17962step2 raw17962step2Labels = mixedMoment B raw17962step3 raw17962step3Labels := by
      have ha : raw17962step3 = raw17962step2 := by apply Matrix.ext; unfold raw17962step3 raw17962step2; decide +kernel
      have hl : raw17962step2Labels = labelEmbedding8 ∘ raw17962step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17962step2 raw17962step2Labels raw17962step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5473 node5473Labels := by rfl

def raw17963 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw17963Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17963step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw17963step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17963step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw17963step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17963 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17963 raw17963Labels = mixedMoment B node4996 node4996Labels := by
  calc
    mixedMoment B raw17963 raw17963Labels = mixedMoment B raw17963step0 raw17963step0Labels := by
      have ha : raw17963step0 = (fun i j => raw17963 (permutation154 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17963step0 raw17963; decide +kernel
      have hl : raw17963step0Labels = raw17963Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17963 raw17963Labels permutation154 permutation3
    mixedMoment B raw17963step0 raw17963step0Labels = mixedMoment B raw17963step1 raw17963step1Labels := by
      have ha : raw17963step1 = raw17963step0 := by apply Matrix.ext; unfold raw17963step1 raw17963step0; decide +kernel
      have hl : raw17963step0Labels = labelEmbedding6 ∘ raw17963step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17963step0 raw17963step0Labels raw17963step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4996 node4996Labels := by rfl

def raw17964 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 3, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw17964Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17964step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw17964step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17964step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw17964step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17964step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw17964step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17964 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17964 raw17964Labels = mixedMoment B node4996 node4996Labels := by
  calc
    mixedMoment B raw17964 raw17964Labels = mixedMoment B raw17964step0 raw17964step0Labels := by
      have ha : raw17964step0 = (fun i j => raw17964 (permutation277 i) (permutation5 j)) := by apply Matrix.ext; unfold raw17964step0 raw17964; decide +kernel
      have hl : raw17964step0Labels = raw17964Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17964 raw17964Labels permutation277 permutation5
    mixedMoment B raw17964step0 raw17964step0Labels = mixedMoment B raw17964step1 raw17964step1Labels := by
      have ha : raw17964step1 = -raw17964step0 := by apply Matrix.ext; change ∀ i j, raw17964step1 i j = -(raw17964step0 i j); unfold raw17964step1 raw17964step0; decide +kernel
      have hl : raw17964step1Labels = raw17964step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17964step1 raw17964step1Labels = mixedMoment B raw17964step2 raw17964step2Labels := by
      have ha : raw17964step2 = raw17964step1 := by apply Matrix.ext; unfold raw17964step2 raw17964step1; decide +kernel
      have hl : raw17964step1Labels = labelEmbedding8 ∘ raw17964step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17964step1 raw17964step1Labels raw17964step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4996 node4996Labels := by rfl

def raw17965 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw17965Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17965step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw17965step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17965step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17965step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17965step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17965step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17965 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17965 raw17965Labels = mixedMoment B node5395 node5395Labels := by
  calc
    mixedMoment B raw17965 raw17965Labels = mixedMoment B raw17965step0 raw17965step0Labels := by
      have ha : raw17965step0 = (fun i j => raw17965 (permutation664 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17965step0 raw17965; decide +kernel
      have hl : raw17965step0Labels = raw17965Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17965 raw17965Labels permutation664 permutation3
    mixedMoment B raw17965step0 raw17965step0Labels = mixedMoment B raw17965step1 raw17965step1Labels := by
      have ha : raw17965step1 = -raw17965step0 := by apply Matrix.ext; change ∀ i j, raw17965step1 i j = -(raw17965step0 i j); unfold raw17965step1 raw17965step0; decide +kernel
      have hl : raw17965step1Labels = raw17965step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17965step1 raw17965step1Labels = mixedMoment B raw17965step2 raw17965step2Labels := by
      have ha : raw17965step2 = raw17965step1 := by apply Matrix.ext; unfold raw17965step2 raw17965step1; decide +kernel
      have hl : raw17965step1Labels = labelEmbedding6 ∘ raw17965step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17965step1 raw17965step1Labels raw17965step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5395 node5395Labels := by rfl

def raw17966 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![2, -2, 0]]
def raw17966Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17966step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17966step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17966step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17966step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17966 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17966 raw17966Labels = mixedMoment B node5395 node5395Labels := by
  calc
    mixedMoment B raw17966 raw17966Labels = mixedMoment B raw17966step0 raw17966step0Labels := by
      have ha : raw17966step0 = (fun i j => raw17966 (permutation657 i) (permutation5 j)) := by apply Matrix.ext; unfold raw17966step0 raw17966; decide +kernel
      have hl : raw17966step0Labels = raw17966Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17966 raw17966Labels permutation657 permutation5
    mixedMoment B raw17966step0 raw17966step0Labels = mixedMoment B raw17966step1 raw17966step1Labels := by
      have ha : raw17966step1 = raw17966step0 := by apply Matrix.ext; unfold raw17966step1 raw17966step0; decide +kernel
      have hl : raw17966step0Labels = labelEmbedding8 ∘ raw17966step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17966step0 raw17966step0Labels raw17966step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5395 node5395Labels := by rfl

def raw17967 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0]]
def raw17967Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17967step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw17967step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17967step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw17967step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17967 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17967 raw17967Labels = mixedMoment B node5472 node5472Labels := by
  calc
    mixedMoment B raw17967 raw17967Labels = mixedMoment B raw17967step0 raw17967step0Labels := by
      have ha : raw17967step0 = (fun i j => raw17967 (permutation154 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17967step0 raw17967; decide +kernel
      have hl : raw17967step0Labels = raw17967Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17967 raw17967Labels permutation154 permutation3
    mixedMoment B raw17967step0 raw17967step0Labels = mixedMoment B raw17967step1 raw17967step1Labels := by
      have ha : raw17967step1 = raw17967step0 := by apply Matrix.ext; unfold raw17967step1 raw17967step0; decide +kernel
      have hl : raw17967step0Labels = labelEmbedding6 ∘ raw17967step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17967step0 raw17967step0Labels raw17967step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5472 node5472Labels := by rfl

def raw17968 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, -1, 1], ![0, 0, 0], ![2, -1, -1], ![2, -2, 0]]
def raw17968Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17968step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, -2, 0]]
def raw17968step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17968step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw17968step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17968step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw17968step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17968 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17968 raw17968Labels = mixedMoment B node5003 node5003Labels := by
  calc
    mixedMoment B raw17968 raw17968Labels = mixedMoment B raw17968step0 raw17968step0Labels := by
      have hz : ∀ j, raw17968 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17968step0 = (fun i j => raw17968 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17968step0 raw17968; decide +kernel
      have hl : raw17968step0Labels = raw17968Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17968 raw17968Labels permutation434 hz
    mixedMoment B raw17968step0 raw17968step0Labels = mixedMoment B raw17968step1 raw17968step1Labels := by
      have ha : raw17968step1 = (fun i j => raw17968step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17968step1 raw17968step0; decide +kernel
      have hl : raw17968step1Labels = raw17968step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17968step0 raw17968step0Labels permutation32 permutation3
    mixedMoment B raw17968step1 raw17968step1Labels = mixedMoment B raw17968step2 raw17968step2Labels := by
      have ha : raw17968step2 = raw17968step1 := by apply Matrix.ext; unfold raw17968step2 raw17968step1; decide +kernel
      have hl : raw17968step1Labels = labelEmbedding6 ∘ raw17968step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17968step1 raw17968step1Labels raw17968step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5003 node5003Labels := by rfl

def raw17969 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 3, -1], ![0, -1, 1], ![0, 0, 0], ![2, -1, -1], ![2, -2, 0]]
def raw17969Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17969step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 3, -1], ![0, -1, 1], ![2, -1, -1], ![2, -2, 0]]
def raw17969step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17969step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw17969step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17969step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw17969step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17969step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw17969step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17969 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17969 raw17969Labels = mixedMoment B node5015 node5015Labels := by
  calc
    mixedMoment B raw17969 raw17969Labels = mixedMoment B raw17969step0 raw17969step0Labels := by
      have hz : ∀ j, raw17969 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17969step0 = (fun i j => raw17969 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17969step0 raw17969; decide +kernel
      have hl : raw17969step0Labels = raw17969Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17969 raw17969Labels permutation434 hz
    mixedMoment B raw17969step0 raw17969step0Labels = mixedMoment B raw17969step1 raw17969step1Labels := by
      have ha : raw17969step1 = (fun i j => raw17969step0 (permutation56 i) (permutation5 j)) := by apply Matrix.ext; unfold raw17969step1 raw17969step0; decide +kernel
      have hl : raw17969step1Labels = raw17969step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17969step0 raw17969step0Labels permutation56 permutation5
    mixedMoment B raw17969step1 raw17969step1Labels = mixedMoment B raw17969step2 raw17969step2Labels := by
      have ha : raw17969step2 = -raw17969step1 := by apply Matrix.ext; change ∀ i j, raw17969step2 i j = -(raw17969step1 i j); unfold raw17969step2 raw17969step1; decide +kernel
      have hl : raw17969step2Labels = raw17969step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17969step2 raw17969step2Labels = mixedMoment B raw17969step3 raw17969step3Labels := by
      have ha : raw17969step3 = raw17969step2 := by apply Matrix.ext; unfold raw17969step3 raw17969step2; decide +kernel
      have hl : raw17969step2Labels = labelEmbedding8 ∘ raw17969step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17969step2 raw17969step2Labels raw17969step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5015 node5015Labels := by rfl

def raw17970 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![-1, 0, 1], ![0, 0, 0], ![2, -1, -1], ![2, -2, 0]]
def raw17970Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17970step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![-1, 0, 1], ![2, -1, -1], ![2, -2, 0]]
def raw17970step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17970step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw17970step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17970step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17970step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17970step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17970step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17970 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17970 raw17970Labels = mixedMoment B node5368 node5368Labels := by
  calc
    mixedMoment B raw17970 raw17970Labels = mixedMoment B raw17970step0 raw17970step0Labels := by
      have hz : ∀ j, raw17970 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17970step0 = (fun i j => raw17970 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17970step0 raw17970; decide +kernel
      have hl : raw17970step0Labels = raw17970Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17970 raw17970Labels permutation434 hz
    mixedMoment B raw17970step0 raw17970step0Labels = mixedMoment B raw17970step1 raw17970step1Labels := by
      have ha : raw17970step1 = (fun i j => raw17970step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17970step1 raw17970step0; decide +kernel
      have hl : raw17970step1Labels = raw17970step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17970step0 raw17970step0Labels permutation151 permutation3
    mixedMoment B raw17970step1 raw17970step1Labels = mixedMoment B raw17970step2 raw17970step2Labels := by
      have ha : raw17970step2 = -raw17970step1 := by apply Matrix.ext; change ∀ i j, raw17970step2 i j = -(raw17970step1 i j); unfold raw17970step2 raw17970step1; decide +kernel
      have hl : raw17970step2Labels = raw17970step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17970step2 raw17970step2Labels = mixedMoment B raw17970step3 raw17970step3Labels := by
      have ha : raw17970step3 = raw17970step2 := by apply Matrix.ext; unfold raw17970step3 raw17970step2; decide +kernel
      have hl : raw17970step2Labels = labelEmbedding6 ∘ raw17970step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17970step2 raw17970step2Labels raw17970step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5368 node5368Labels := by rfl

def raw17971 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![-1, 1, 0], ![2, -1, -1], ![2, -2, 0]]
def raw17971Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17971step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw17971step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17971step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17971step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17971step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17971step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17971 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17971 raw17971Labels = mixedMoment B node5346 node5346Labels := by
  calc
    mixedMoment B raw17971 raw17971Labels = mixedMoment B raw17971step0 raw17971step0Labels := by
      have ha : raw17971step0 = (fun i j => raw17971 (permutation682 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17971step0 raw17971; decide +kernel
      have hl : raw17971step0Labels = raw17971Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17971 raw17971Labels permutation682 permutation3
    mixedMoment B raw17971step0 raw17971step0Labels = mixedMoment B raw17971step1 raw17971step1Labels := by
      have ha : raw17971step1 = -raw17971step0 := by apply Matrix.ext; change ∀ i j, raw17971step1 i j = -(raw17971step0 i j); unfold raw17971step1 raw17971step0; decide +kernel
      have hl : raw17971step1Labels = raw17971step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17971step1 raw17971step1Labels = mixedMoment B raw17971step2 raw17971step2Labels := by
      have ha : raw17971step2 = raw17971step1 := by apply Matrix.ext; unfold raw17971step2 raw17971step1; decide +kernel
      have hl : raw17971step1Labels = labelEmbedding6 ∘ raw17971step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17971step1 raw17971step1Labels raw17971step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5346 node5346Labels := by rfl

def raw17972 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![0, 0, 0], ![2, -1, -1], ![1, -1, 0]]
def raw17972Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17972step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![1, -1, 0]]
def raw17972step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17972step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17972step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17972step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17972step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17972 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17972 raw17972Labels = mixedMoment B node5473 node5473Labels := by
  calc
    mixedMoment B raw17972 raw17972Labels = mixedMoment B raw17972step0 raw17972step0Labels := by
      have hz : ∀ j, raw17972 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17972step0 = (fun i j => raw17972 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17972step0 raw17972; decide +kernel
      have hl : raw17972step0Labels = raw17972Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17972 raw17972Labels permutation434 hz
    mixedMoment B raw17972step0 raw17972step0Labels = mixedMoment B raw17972step1 raw17972step1Labels := by
      have ha : raw17972step1 = (fun i j => raw17972step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17972step1 raw17972step0; decide +kernel
      have hl : raw17972step1Labels = raw17972step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17972step0 raw17972step0Labels permutation33 permutation3
    mixedMoment B raw17972step1 raw17972step1Labels = mixedMoment B raw17972step2 raw17972step2Labels := by
      have ha : raw17972step2 = raw17972step1 := by apply Matrix.ext; unfold raw17972step2 raw17972step1; decide +kernel
      have hl : raw17972step1Labels = labelEmbedding6 ∘ raw17972step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17972step1 raw17972step1Labels raw17972step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5473 node5473Labels := by rfl

def raw17973 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![3, -3, 0]]
def raw17973Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17973step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![3, -3, 0]]
def raw17973step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17973step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-3, 1, 2]]
def raw17973step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17973step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw17973step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17973step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw17973step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17973 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17973 raw17973Labels = mixedMoment B node4788 node4788Labels := by
  calc
    mixedMoment B raw17973 raw17973Labels = mixedMoment B raw17973step0 raw17973step0Labels := by
      have hz : ∀ j, raw17973 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17973step0 = (fun i j => raw17973 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17973step0 raw17973; decide +kernel
      have hl : raw17973step0Labels = raw17973Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17973 raw17973Labels permutation434 hz
    mixedMoment B raw17973step0 raw17973step0Labels = mixedMoment B raw17973step1 raw17973step1Labels := by
      have ha : raw17973step1 = (fun i j => raw17973step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17973step1 raw17973step0; decide +kernel
      have hl : raw17973step1Labels = raw17973step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17973step0 raw17973step0Labels permutation151 permutation3
    mixedMoment B raw17973step1 raw17973step1Labels = mixedMoment B raw17973step2 raw17973step2Labels := by
      have ha : raw17973step2 = -raw17973step1 := by apply Matrix.ext; change ∀ i j, raw17973step2 i j = -(raw17973step1 i j); unfold raw17973step2 raw17973step1; decide +kernel
      have hl : raw17973step2Labels = raw17973step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17973step2 raw17973step2Labels = mixedMoment B raw17973step3 raw17973step3Labels := by
      have ha : raw17973step3 = raw17973step2 := by apply Matrix.ext; unfold raw17973step3 raw17973step2; decide +kernel
      have hl : raw17973step2Labels = labelEmbedding6 ∘ raw17973step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17973step2 raw17973step2Labels raw17973step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4788 node4788Labels := by rfl

def raw17974 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 3, -1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![3, -3, 0]]
def raw17974Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17974step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 3, -1], ![0, -1, 1], ![1, 0, -1], ![3, -3, 0]]
def raw17974step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17974step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw17974step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17974step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw17974step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17974 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17974 raw17974Labels = mixedMoment B node4788 node4788Labels := by
  calc
    mixedMoment B raw17974 raw17974Labels = mixedMoment B raw17974step0 raw17974step0Labels := by
      have hz : ∀ j, raw17974 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17974step0 = (fun i j => raw17974 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17974step0 raw17974; decide +kernel
      have hl : raw17974step0Labels = raw17974Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17974 raw17974Labels permutation434 hz
    mixedMoment B raw17974step0 raw17974step0Labels = mixedMoment B raw17974step1 raw17974step1Labels := by
      have ha : raw17974step1 = (fun i j => raw17974step0 (permutation144 i) (permutation5 j)) := by apply Matrix.ext; unfold raw17974step1 raw17974step0; decide +kernel
      have hl : raw17974step1Labels = raw17974step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17974step0 raw17974step0Labels permutation144 permutation5
    mixedMoment B raw17974step1 raw17974step1Labels = mixedMoment B raw17974step2 raw17974step2Labels := by
      have ha : raw17974step2 = raw17974step1 := by apply Matrix.ext; unfold raw17974step2 raw17974step1; decide +kernel
      have hl : raw17974step1Labels = labelEmbedding8 ∘ raw17974step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17974step1 raw17974step1Labels raw17974step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4788 node4788Labels := by rfl

def raw17975 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![3, -3, 0]]
def raw17975Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17975step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![-1, 0, 1], ![1, 0, -1], ![3, -3, 0]]
def raw17975step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17975step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw17975step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17975step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17975step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17975step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17975step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17975 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17975 raw17975Labels = mixedMoment B node4835 node4835Labels := by
  calc
    mixedMoment B raw17975 raw17975Labels = mixedMoment B raw17975step0 raw17975step0Labels := by
      have hz : ∀ j, raw17975 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17975step0 = (fun i j => raw17975 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17975step0 raw17975; decide +kernel
      have hl : raw17975step0Labels = raw17975Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17975 raw17975Labels permutation434 hz
    mixedMoment B raw17975step0 raw17975step0Labels = mixedMoment B raw17975step1 raw17975step1Labels := by
      have ha : raw17975step1 = (fun i j => raw17975step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17975step1 raw17975step0; decide +kernel
      have hl : raw17975step1Labels = raw17975step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17975step0 raw17975step0Labels permutation151 permutation3
    mixedMoment B raw17975step1 raw17975step1Labels = mixedMoment B raw17975step2 raw17975step2Labels := by
      have ha : raw17975step2 = -raw17975step1 := by apply Matrix.ext; change ∀ i j, raw17975step2 i j = -(raw17975step1 i j); unfold raw17975step2 raw17975step1; decide +kernel
      have hl : raw17975step2Labels = raw17975step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17975step2 raw17975step2Labels = mixedMoment B raw17975step3 raw17975step3Labels := by
      have ha : raw17975step3 = raw17975step2 := by apply Matrix.ext; unfold raw17975step3 raw17975step2; decide +kernel
      have hl : raw17975step2Labels = labelEmbedding6 ∘ raw17975step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17975step2 raw17975step2Labels raw17975step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4835 node4835Labels := by rfl

def raw17976 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![-1, 1, 0], ![1, 0, -1], ![3, -3, 0]]
def raw17976Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17976step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw17976step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17976step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17976step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17976step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17976step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17976 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17976 raw17976Labels = mixedMoment B node4787 node4787Labels := by
  calc
    mixedMoment B raw17976 raw17976Labels = mixedMoment B raw17976step0 raw17976step0Labels := by
      have ha : raw17976step0 = (fun i j => raw17976 (permutation682 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17976step0 raw17976; decide +kernel
      have hl : raw17976step0Labels = raw17976Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17976 raw17976Labels permutation682 permutation3
    mixedMoment B raw17976step0 raw17976step0Labels = mixedMoment B raw17976step1 raw17976step1Labels := by
      have ha : raw17976step1 = -raw17976step0 := by apply Matrix.ext; change ∀ i j, raw17976step1 i j = -(raw17976step0 i j); unfold raw17976step1 raw17976step0; decide +kernel
      have hl : raw17976step1Labels = raw17976step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17976step1 raw17976step1Labels = mixedMoment B raw17976step2 raw17976step2Labels := by
      have ha : raw17976step2 = raw17976step1 := by apply Matrix.ext; unfold raw17976step2 raw17976step1; decide +kernel
      have hl : raw17976step1Labels = labelEmbedding6 ∘ raw17976step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17976step1 raw17976step1Labels raw17976step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4787 node4787Labels := by rfl

def raw17977 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![3, -3, 0]]
def raw17977Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17977step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![3, -3, 0]]
def raw17977step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17977step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17977step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17977step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17977step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17977 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17977 raw17977Labels = mixedMoment B node4835 node4835Labels := by
  calc
    mixedMoment B raw17977 raw17977Labels = mixedMoment B raw17977step0 raw17977step0Labels := by
      have hz : ∀ j, raw17977 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17977step0 = (fun i j => raw17977 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17977step0 raw17977; decide +kernel
      have hl : raw17977step0Labels = raw17977Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17977 raw17977Labels permutation434 hz
    mixedMoment B raw17977step0 raw17977step0Labels = mixedMoment B raw17977step1 raw17977step1Labels := by
      have ha : raw17977step1 = (fun i j => raw17977step0 (permutation144 i) (permutation5 j)) := by apply Matrix.ext; unfold raw17977step1 raw17977step0; decide +kernel
      have hl : raw17977step1Labels = raw17977step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17977step0 raw17977step0Labels permutation144 permutation5
    mixedMoment B raw17977step1 raw17977step1Labels = mixedMoment B raw17977step2 raw17977step2Labels := by
      have ha : raw17977step2 = raw17977step1 := by apply Matrix.ext; unfold raw17977step2 raw17977step1; decide +kernel
      have hl : raw17977step1Labels = labelEmbedding8 ∘ raw17977step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17977step1 raw17977step1Labels raw17977step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4835 node4835Labels := by rfl

def raw17978 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17978Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17978step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17978step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17978step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![1, 1, -2], ![2, -1, -1]]
def raw17978step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17978step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17978step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17978 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17978 raw17978Labels = mixedMoment B node5413 node5413Labels := by
  calc
    mixedMoment B raw17978 raw17978Labels = mixedMoment B raw17978step0 raw17978step0Labels := by
      have hz : ∀ j, raw17978 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17978step0 = (fun i j => raw17978 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17978step0 raw17978; decide +kernel
      have hl : raw17978step0Labels = raw17978Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17978 raw17978Labels permutation434 hz
    mixedMoment B raw17978step0 raw17978step0Labels = mixedMoment B raw17978step1 raw17978step1Labels := by
      have hz : ∀ j, raw17978step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw17978step1 = (fun i j => raw17978step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw17978step1 raw17978step0; decide +kernel
      have hl : raw17978step1Labels = raw17978step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17978step0 raw17978step0Labels permutation80 hz
    mixedMoment B raw17978step1 raw17978step1Labels = mixedMoment B raw17978step2 raw17978step2Labels := by
      have ha : raw17978step2 = (fun i j => raw17978step1 (permutation14 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17978step2 raw17978step1; decide +kernel
      have hl : raw17978step2Labels = raw17978step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17978step1 raw17978step1Labels permutation14 permutation2
    _ = mixedMoment B node5413 node5413Labels := by rfl

def raw17979 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17979Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17979step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17979step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17979step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17979step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw17979step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17979step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17979 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17979 raw17979Labels = mixedMoment B node5473 node5473Labels := by
  calc
    mixedMoment B raw17979 raw17979Labels = mixedMoment B raw17979step0 raw17979step0Labels := by
      have hz : ∀ j, raw17979 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17979step0 = (fun i j => raw17979 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17979step0 raw17979; decide +kernel
      have hl : raw17979step0Labels = raw17979Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17979 raw17979Labels permutation434 hz
    mixedMoment B raw17979step0 raw17979step0Labels = mixedMoment B raw17979step1 raw17979step1Labels := by
      have ha : raw17979step1 = (fun i j => raw17979step0 (permutation126 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17979step1 raw17979step0; decide +kernel
      have hl : raw17979step1Labels = raw17979step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17979step0 raw17979step0Labels permutation126 permutation7
    mixedMoment B raw17979step1 raw17979step1Labels = mixedMoment B raw17979step2 raw17979step2Labels := by
      have ha : raw17979step2 = raw17979step1 := by apply Matrix.ext; unfold raw17979step2 raw17979step1; decide +kernel
      have hl : raw17979step1Labels = labelEmbedding10 ∘ raw17979step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17979step1 raw17979step1Labels raw17979step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5473 node5473Labels := by rfl

def raw17980 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17980Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17980step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17980step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17980step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17980step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw17980step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17980step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17980 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17980 raw17980Labels = mixedMoment B node5473 node5473Labels := by
  calc
    mixedMoment B raw17980 raw17980Labels = mixedMoment B raw17980step0 raw17980step0Labels := by
      have hz : ∀ j, raw17980 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17980step0 = (fun i j => raw17980 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17980step0 raw17980; decide +kernel
      have hl : raw17980step0Labels = raw17980Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17980 raw17980Labels permutation346 hz
    mixedMoment B raw17980step0 raw17980step0Labels = mixedMoment B raw17980step1 raw17980step1Labels := by
      have ha : raw17980step1 = (fun i j => raw17980step0 (permutation126 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17980step1 raw17980step0; decide +kernel
      have hl : raw17980step1Labels = raw17980step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17980step0 raw17980step0Labels permutation126 permutation7
    mixedMoment B raw17980step1 raw17980step1Labels = mixedMoment B raw17980step2 raw17980step2Labels := by
      have ha : raw17980step2 = raw17980step1 := by apply Matrix.ext; unfold raw17980step2 raw17980step1; decide +kernel
      have hl : raw17980step1Labels = labelEmbedding10 ∘ raw17980step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17980step1 raw17980step1Labels raw17980step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5473 node5473Labels := by rfl

def raw17981 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![2, -1, -1]]
def raw17981Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17981step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 2, -2], ![2, -1, -1]]
def raw17981step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17981step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 2, -2], ![2, -1, -1]]
def raw17981step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17981step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17981step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw17981step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17981step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17981 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17981 raw17981Labels = mixedMoment B node5451 node5451Labels := by
  calc
    mixedMoment B raw17981 raw17981Labels = mixedMoment B raw17981step0 raw17981step0Labels := by
      have hz : ∀ j, raw17981 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17981step0 = (fun i j => raw17981 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17981step0 raw17981; decide +kernel
      have hl : raw17981step0Labels = raw17981Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17981 raw17981Labels permutation434 hz
    mixedMoment B raw17981step0 raw17981step0Labels = mixedMoment B raw17981step1 raw17981step1Labels := by
      have hz : ∀ j, raw17981step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw17981step1 = (fun i j => raw17981step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw17981step1 raw17981step0; decide +kernel
      have hl : raw17981step1Labels = raw17981step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17981step0 raw17981step0Labels permutation80 hz
    mixedMoment B raw17981step1 raw17981step1Labels = mixedMoment B raw17981step2 raw17981step2Labels := by
      have ha : raw17981step2 = (fun i j => raw17981step1 (permutation24 i) (permutation6 j)) := by apply Matrix.ext; unfold raw17981step2 raw17981step1; decide +kernel
      have hl : raw17981step2Labels = raw17981step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17981step1 raw17981step1Labels permutation24 permutation6
    mixedMoment B raw17981step2 raw17981step2Labels = mixedMoment B raw17981step3 raw17981step3Labels := by
      have ha : raw17981step3 = raw17981step2 := by apply Matrix.ext; unfold raw17981step3 raw17981step2; decide +kernel
      have hl : raw17981step2Labels = labelEmbedding9 ∘ raw17981step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17981step2 raw17981step2Labels raw17981step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5451 node5451Labels := by rfl

def raw17982 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1]]
def raw17982Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17982step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1]]
def raw17982step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17982step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![1, 1, -2], ![1, 0, -1]]
def raw17982step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17982step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw17982step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw17982step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw17982step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17982 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17982 raw17982Labels = mixedMoment B node5487 node5487Labels := by
  calc
    mixedMoment B raw17982 raw17982Labels = mixedMoment B raw17982step0 raw17982step0Labels := by
      have hz : ∀ j, raw17982 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17982step0 = (fun i j => raw17982 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17982step0 raw17982; decide +kernel
      have hl : raw17982step0Labels = raw17982Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17982 raw17982Labels permutation434 hz
    mixedMoment B raw17982step0 raw17982step0Labels = mixedMoment B raw17982step1 raw17982step1Labels := by
      have hz : ∀ j, raw17982step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw17982step1 = (fun i j => raw17982step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw17982step1 raw17982step0; decide +kernel
      have hl : raw17982step1Labels = raw17982step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17982step0 raw17982step0Labels permutation80 hz
    mixedMoment B raw17982step1 raw17982step1Labels = mixedMoment B raw17982step2 raw17982step2Labels := by
      have ha : raw17982step2 = (fun i j => raw17982step1 (permutation24 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17982step2 raw17982step1; decide +kernel
      have hl : raw17982step2Labels = raw17982step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17982step1 raw17982step1Labels permutation24 permutation7
    mixedMoment B raw17982step2 raw17982step2Labels = mixedMoment B raw17982step3 raw17982step3Labels := by
      have ha : raw17982step3 = raw17982step2 := by apply Matrix.ext; unfold raw17982step3 raw17982step2; decide +kernel
      have hl : raw17982step2Labels = labelEmbedding10 ∘ raw17982step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17982step2 raw17982step2Labels raw17982step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5487 node5487Labels := by rfl

def raw17983 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17983Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17983step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17983step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17983step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw17983step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17983step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw17983step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17983step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw17983step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17983 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17983 raw17983Labels = mixedMoment B node5300 node5300Labels := by
  calc
    mixedMoment B raw17983 raw17983Labels = mixedMoment B raw17983step0 raw17983step0Labels := by
      have hz : ∀ j, raw17983 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17983step0 = (fun i j => raw17983 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17983step0 raw17983; decide +kernel
      have hl : raw17983step0Labels = raw17983Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17983 raw17983Labels permutation434 hz
    mixedMoment B raw17983step0 raw17983step0Labels = mixedMoment B raw17983step1 raw17983step1Labels := by
      have hz : ∀ j, raw17983step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw17983step1 = (fun i j => raw17983step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw17983step1 raw17983step0; decide +kernel
      have hl : raw17983step1Labels = raw17983step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17983step0 raw17983step0Labels permutation80 hz
    mixedMoment B raw17983step1 raw17983step1Labels = mixedMoment B raw17983step2 raw17983step2Labels := by
      have ha : raw17983step2 = (fun i j => raw17983step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17983step2 raw17983step1; decide +kernel
      have hl : raw17983step2Labels = raw17983step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17983step1 raw17983step1Labels permutation8 permutation3
    mixedMoment B raw17983step2 raw17983step2Labels = mixedMoment B raw17983step3 raw17983step3Labels := by
      have ha : raw17983step3 = raw17983step2 := by apply Matrix.ext; unfold raw17983step3 raw17983step2; decide +kernel
      have hl : raw17983step2Labels = labelEmbedding6 ∘ raw17983step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17983step2 raw17983step2Labels raw17983step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5300 node5300Labels := by rfl

def raw17984 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17984Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17984step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17984step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17984step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw17984step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw17984step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17984step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw17984step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17984step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17984 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17984 raw17984Labels = mixedMoment B node5446 node5446Labels := by
  calc
    mixedMoment B raw17984 raw17984Labels = mixedMoment B raw17984step0 raw17984step0Labels := by
      have hz : ∀ j, raw17984 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17984step0 = (fun i j => raw17984 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17984step0 raw17984; decide +kernel
      have hl : raw17984step0Labels = raw17984Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17984 raw17984Labels permutation434 hz
    mixedMoment B raw17984step0 raw17984step0Labels = mixedMoment B raw17984step1 raw17984step1Labels := by
      have ha : raw17984step1 = (fun i j => raw17984step0 (permutation57 i) (permutation6 j)) := by apply Matrix.ext; unfold raw17984step1 raw17984step0; decide +kernel
      have hl : raw17984step1Labels = raw17984step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17984step0 raw17984step0Labels permutation57 permutation6
    mixedMoment B raw17984step1 raw17984step1Labels = mixedMoment B raw17984step2 raw17984step2Labels := by
      have ha : raw17984step2 = -raw17984step1 := by apply Matrix.ext; change ∀ i j, raw17984step2 i j = -(raw17984step1 i j); unfold raw17984step2 raw17984step1; decide +kernel
      have hl : raw17984step2Labels = raw17984step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17984step2 raw17984step2Labels = mixedMoment B raw17984step3 raw17984step3Labels := by
      have ha : raw17984step3 = raw17984step2 := by apply Matrix.ext; unfold raw17984step3 raw17984step2; decide +kernel
      have hl : raw17984step2Labels = labelEmbedding9 ∘ raw17984step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17984step2 raw17984step2Labels raw17984step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5446 node5446Labels := by rfl

def raw17985 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17985Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17985step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17985step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17985step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw17985step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw17985step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17985step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw17985step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17985step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17985 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17985 raw17985Labels = mixedMoment B node5446 node5446Labels := by
  calc
    mixedMoment B raw17985 raw17985Labels = mixedMoment B raw17985step0 raw17985step0Labels := by
      have hz : ∀ j, raw17985 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17985step0 = (fun i j => raw17985 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17985step0 raw17985; decide +kernel
      have hl : raw17985step0Labels = raw17985Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17985 raw17985Labels permutation346 hz
    mixedMoment B raw17985step0 raw17985step0Labels = mixedMoment B raw17985step1 raw17985step1Labels := by
      have ha : raw17985step1 = (fun i j => raw17985step0 (permutation57 i) (permutation6 j)) := by apply Matrix.ext; unfold raw17985step1 raw17985step0; decide +kernel
      have hl : raw17985step1Labels = raw17985step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17985step0 raw17985step0Labels permutation57 permutation6
    mixedMoment B raw17985step1 raw17985step1Labels = mixedMoment B raw17985step2 raw17985step2Labels := by
      have ha : raw17985step2 = -raw17985step1 := by apply Matrix.ext; change ∀ i j, raw17985step2 i j = -(raw17985step1 i j); unfold raw17985step2 raw17985step1; decide +kernel
      have hl : raw17985step2Labels = raw17985step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17985step2 raw17985step2Labels = mixedMoment B raw17985step3 raw17985step3Labels := by
      have ha : raw17985step3 = raw17985step2 := by apply Matrix.ext; unfold raw17985step3 raw17985step2; decide +kernel
      have hl : raw17985step2Labels = labelEmbedding9 ∘ raw17985step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17985step2 raw17985step2Labels raw17985step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5446 node5446Labels := by rfl

def raw17986 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![2, -1, -1]]
def raw17986Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17986step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 0, 0], ![0, 2, -2], ![2, -1, -1]]
def raw17986step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17986step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 2, -2], ![2, -1, -1]]
def raw17986step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17986step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![2, 0, -2]]
def raw17986step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17986step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![2, 0, -2]]
def raw17986step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17986 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17986 raw17986Labels = mixedMoment B node5449 node5449Labels := by
  calc
    mixedMoment B raw17986 raw17986Labels = mixedMoment B raw17986step0 raw17986step0Labels := by
      have hz : ∀ j, raw17986 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17986step0 = (fun i j => raw17986 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17986step0 raw17986; decide +kernel
      have hl : raw17986step0Labels = raw17986Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17986 raw17986Labels permutation434 hz
    mixedMoment B raw17986step0 raw17986step0Labels = mixedMoment B raw17986step1 raw17986step1Labels := by
      have hz : ∀ j, raw17986step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw17986step1 = (fun i j => raw17986step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw17986step1 raw17986step0; decide +kernel
      have hl : raw17986step1Labels = raw17986step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17986step0 raw17986step0Labels permutation80 hz
    mixedMoment B raw17986step1 raw17986step1Labels = mixedMoment B raw17986step2 raw17986step2Labels := by
      have ha : raw17986step2 = (fun i j => raw17986step1 (permutation18 i) (permutation4 j)) := by apply Matrix.ext; unfold raw17986step2 raw17986step1; decide +kernel
      have hl : raw17986step2Labels = raw17986step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17986step1 raw17986step1Labels permutation18 permutation4
    mixedMoment B raw17986step2 raw17986step2Labels = mixedMoment B raw17986step3 raw17986step3Labels := by
      have ha : raw17986step3 = raw17986step2 := by apply Matrix.ext; unfold raw17986step3 raw17986step2; decide +kernel
      have hl : raw17986step2Labels = labelEmbedding7 ∘ raw17986step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17986step2 raw17986step2Labels raw17986step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5449 node5449Labels := by rfl

def raw17987 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1]]
def raw17987Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17987step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1]]
def raw17987step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17987step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1]]
def raw17987step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17987step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw17987step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw17987step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17987step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw17987step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17987step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17987 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17987 raw17987Labels = mixedMoment B node5451 node5451Labels := by
  calc
    mixedMoment B raw17987 raw17987Labels = mixedMoment B raw17987step0 raw17987step0Labels := by
      have hz : ∀ j, raw17987 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17987step0 = (fun i j => raw17987 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17987step0 raw17987; decide +kernel
      have hl : raw17987step0Labels = raw17987Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17987 raw17987Labels permutation434 hz
    mixedMoment B raw17987step0 raw17987step0Labels = mixedMoment B raw17987step1 raw17987step1Labels := by
      have hz : ∀ j, raw17987step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw17987step1 = (fun i j => raw17987step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw17987step1 raw17987step0; decide +kernel
      have hl : raw17987step1Labels = raw17987step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17987step0 raw17987step0Labels permutation80 hz
    mixedMoment B raw17987step1 raw17987step1Labels = mixedMoment B raw17987step2 raw17987step2Labels := by
      have ha : raw17987step2 = (fun i j => raw17987step1 (permutation15 i) (permutation6 j)) := by apply Matrix.ext; unfold raw17987step2 raw17987step1; decide +kernel
      have hl : raw17987step2Labels = raw17987step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17987step1 raw17987step1Labels permutation15 permutation6
    mixedMoment B raw17987step2 raw17987step2Labels = mixedMoment B raw17987step3 raw17987step3Labels := by
      have ha : raw17987step3 = -raw17987step2 := by apply Matrix.ext; change ∀ i j, raw17987step3 i j = -(raw17987step2 i j); unfold raw17987step3 raw17987step2; decide +kernel
      have hl : raw17987step3Labels = raw17987step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17987step3 raw17987step3Labels = mixedMoment B raw17987step4 raw17987step4Labels := by
      have ha : raw17987step4 = raw17987step3 := by apply Matrix.ext; unfold raw17987step4 raw17987step3; decide +kernel
      have hl : raw17987step3Labels = labelEmbedding9 ∘ raw17987step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17987step3 raw17987step3Labels raw17987step4Labels labelEmbedding9 hl
    _ = mixedMoment B node5451 node5451Labels := by rfl

def raw17988 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17988Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17988step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17988step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17988step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw17988step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17988step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw17988step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17988 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17988 raw17988Labels = mixedMoment B node5199 node5199Labels := by
  calc
    mixedMoment B raw17988 raw17988Labels = mixedMoment B raw17988step0 raw17988step0Labels := by
      have hz : ∀ j, raw17988 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17988step0 = (fun i j => raw17988 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17988step0 raw17988; decide +kernel
      have hl : raw17988step0Labels = raw17988Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17988 raw17988Labels permutation434 hz
    mixedMoment B raw17988step0 raw17988step0Labels = mixedMoment B raw17988step1 raw17988step1Labels := by
      have ha : raw17988step1 = (fun i j => raw17988step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17988step1 raw17988step0; decide +kernel
      have hl : raw17988step1Labels = raw17988step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17988step0 raw17988step0Labels permutation34 permutation3
    mixedMoment B raw17988step1 raw17988step1Labels = mixedMoment B raw17988step2 raw17988step2Labels := by
      have ha : raw17988step2 = raw17988step1 := by apply Matrix.ext; unfold raw17988step2 raw17988step1; decide +kernel
      have hl : raw17988step1Labels = labelEmbedding6 ∘ raw17988step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17988step1 raw17988step1Labels raw17988step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5199 node5199Labels := by rfl

def raw17989 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17989Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17989step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17989step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17989step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17989step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17989 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17989 raw17989Labels = mixedMoment B node5368 node5368Labels := by
  calc
    mixedMoment B raw17989 raw17989Labels = mixedMoment B raw17989step0 raw17989step0Labels := by
      have hz : ∀ j, raw17989 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17989step0 = (fun i j => raw17989 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17989step0 raw17989; decide +kernel
      have hl : raw17989step0Labels = raw17989Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17989 raw17989Labels permutation434 hz
    mixedMoment B raw17989step0 raw17989step0Labels = mixedMoment B raw17989step1 raw17989step1Labels := by
      have ha : raw17989step1 = (fun i j => raw17989step0 (permutation56 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17989step1 raw17989step0; decide +kernel
      have hl : raw17989step1Labels = raw17989step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17989step0 raw17989step0Labels permutation56 permutation2
    _ = mixedMoment B node5368 node5368Labels := by rfl

def raw17990 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17990Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17990step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17990step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17990 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17990 raw17990Labels = mixedMoment B node5468 node5468Labels := by
  calc
    mixedMoment B raw17990 raw17990Labels = mixedMoment B raw17990step0 raw17990step0Labels := by
      have ha : raw17990step0 = (fun i j => raw17990 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17990step0 raw17990; decide +kernel
      have hl : raw17990step0Labels = raw17990Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17990 raw17990Labels permutation158 permutation2
    _ = mixedMoment B node5468 node5468Labels := by rfl

def raw17991 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 2, -2], ![2, -1, -1]]
def raw17991Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17991step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![0, 2, -2], ![2, -1, -1]]
def raw17991step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17991step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17991step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw17991step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17991step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17991 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17991 raw17991Labels = mixedMoment B node5446 node5446Labels := by
  calc
    mixedMoment B raw17991 raw17991Labels = mixedMoment B raw17991step0 raw17991step0Labels := by
      have hz : ∀ j, raw17991 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17991step0 = (fun i j => raw17991 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17991step0 raw17991; decide +kernel
      have hl : raw17991step0Labels = raw17991Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17991 raw17991Labels permutation434 hz
    mixedMoment B raw17991step0 raw17991step0Labels = mixedMoment B raw17991step1 raw17991step1Labels := by
      have ha : raw17991step1 = (fun i j => raw17991step0 (permutation126 i) (permutation6 j)) := by apply Matrix.ext; unfold raw17991step1 raw17991step0; decide +kernel
      have hl : raw17991step1Labels = raw17991step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17991step0 raw17991step0Labels permutation126 permutation6
    mixedMoment B raw17991step1 raw17991step1Labels = mixedMoment B raw17991step2 raw17991step2Labels := by
      have ha : raw17991step2 = raw17991step1 := by apply Matrix.ext; unfold raw17991step2 raw17991step1; decide +kernel
      have hl : raw17991step1Labels = labelEmbedding9 ∘ raw17991step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17991step1 raw17991step1Labels raw17991step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5446 node5446Labels := by rfl

def raw17992 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1]]
def raw17992Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17992step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1]]
def raw17992step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17992step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17992step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw17992step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17992step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw17992step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17992step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17992 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17992 raw17992Labels = mixedMoment B node5473 node5473Labels := by
  calc
    mixedMoment B raw17992 raw17992Labels = mixedMoment B raw17992step0 raw17992step0Labels := by
      have hz : ∀ j, raw17992 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17992step0 = (fun i j => raw17992 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17992step0 raw17992; decide +kernel
      have hl : raw17992step0Labels = raw17992Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17992 raw17992Labels permutation434 hz
    mixedMoment B raw17992step0 raw17992step0Labels = mixedMoment B raw17992step1 raw17992step1Labels := by
      have ha : raw17992step1 = (fun i j => raw17992step0 (permutation57 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17992step1 raw17992step0; decide +kernel
      have hl : raw17992step1Labels = raw17992step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17992step0 raw17992step0Labels permutation57 permutation7
    mixedMoment B raw17992step1 raw17992step1Labels = mixedMoment B raw17992step2 raw17992step2Labels := by
      have ha : raw17992step2 = -raw17992step1 := by apply Matrix.ext; change ∀ i j, raw17992step2 i j = -(raw17992step1 i j); unfold raw17992step2 raw17992step1; decide +kernel
      have hl : raw17992step2Labels = raw17992step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17992step2 raw17992step2Labels = mixedMoment B raw17992step3 raw17992step3Labels := by
      have ha : raw17992step3 = raw17992step2 := by apply Matrix.ext; unfold raw17992step3 raw17992step2; decide +kernel
      have hl : raw17992step2Labels = labelEmbedding10 ∘ raw17992step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17992step2 raw17992step2Labels raw17992step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5473 node5473Labels := by rfl

def raw17993 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17993Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17993step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17993step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17993step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw17993step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17993step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw17993step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17993 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17993 raw17993Labels = mixedMoment B node5199 node5199Labels := by
  calc
    mixedMoment B raw17993 raw17993Labels = mixedMoment B raw17993step0 raw17993step0Labels := by
      have hz : ∀ j, raw17993 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17993step0 = (fun i j => raw17993 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17993step0 raw17993; decide +kernel
      have hl : raw17993step0Labels = raw17993Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17993 raw17993Labels permutation346 hz
    mixedMoment B raw17993step0 raw17993step0Labels = mixedMoment B raw17993step1 raw17993step1Labels := by
      have ha : raw17993step1 = (fun i j => raw17993step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17993step1 raw17993step0; decide +kernel
      have hl : raw17993step1Labels = raw17993step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17993step0 raw17993step0Labels permutation34 permutation3
    mixedMoment B raw17993step1 raw17993step1Labels = mixedMoment B raw17993step2 raw17993step2Labels := by
      have ha : raw17993step2 = raw17993step1 := by apply Matrix.ext; unfold raw17993step2 raw17993step1; decide +kernel
      have hl : raw17993step1Labels = labelEmbedding6 ∘ raw17993step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17993step1 raw17993step1Labels raw17993step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5199 node5199Labels := by rfl

def raw17994 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17994Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17994step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17994step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17994step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17994step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17994 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17994 raw17994Labels = mixedMoment B node5368 node5368Labels := by
  calc
    mixedMoment B raw17994 raw17994Labels = mixedMoment B raw17994step0 raw17994step0Labels := by
      have hz : ∀ j, raw17994 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17994step0 = (fun i j => raw17994 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17994step0 raw17994; decide +kernel
      have hl : raw17994step0Labels = raw17994Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17994 raw17994Labels permutation346 hz
    mixedMoment B raw17994step0 raw17994step0Labels = mixedMoment B raw17994step1 raw17994step1Labels := by
      have ha : raw17994step1 = (fun i j => raw17994step0 (permutation56 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17994step1 raw17994step0; decide +kernel
      have hl : raw17994step1Labels = raw17994step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17994step0 raw17994step0Labels permutation56 permutation2
    _ = mixedMoment B node5368 node5368Labels := by rfl

def raw17995 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17995Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17995 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17995 raw17995Labels = mixedMoment B node5468 node5468Labels := by
  calc
    _ = mixedMoment B node5468 node5468Labels := by rfl

def raw17996 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![2, -1, -1]]
def raw17996Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17996step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![0, 2, -2], ![2, -1, -1]]
def raw17996step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17996step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17996step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw17996step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17996step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17996 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17996 raw17996Labels = mixedMoment B node5446 node5446Labels := by
  calc
    mixedMoment B raw17996 raw17996Labels = mixedMoment B raw17996step0 raw17996step0Labels := by
      have hz : ∀ j, raw17996 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17996step0 = (fun i j => raw17996 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17996step0 raw17996; decide +kernel
      have hl : raw17996step0Labels = raw17996Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17996 raw17996Labels permutation346 hz
    mixedMoment B raw17996step0 raw17996step0Labels = mixedMoment B raw17996step1 raw17996step1Labels := by
      have ha : raw17996step1 = (fun i j => raw17996step0 (permutation126 i) (permutation6 j)) := by apply Matrix.ext; unfold raw17996step1 raw17996step0; decide +kernel
      have hl : raw17996step1Labels = raw17996step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17996step0 raw17996step0Labels permutation126 permutation6
    mixedMoment B raw17996step1 raw17996step1Labels = mixedMoment B raw17996step2 raw17996step2Labels := by
      have ha : raw17996step2 = raw17996step1 := by apply Matrix.ext; unfold raw17996step2 raw17996step1; decide +kernel
      have hl : raw17996step1Labels = labelEmbedding9 ∘ raw17996step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17996step1 raw17996step1Labels raw17996step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5446 node5446Labels := by rfl

def raw17997 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1]]
def raw17997Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17997step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1]]
def raw17997step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17997step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17997step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw17997step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17997step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw17997step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17997step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17997 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17997 raw17997Labels = mixedMoment B node5473 node5473Labels := by
  calc
    mixedMoment B raw17997 raw17997Labels = mixedMoment B raw17997step0 raw17997step0Labels := by
      have hz : ∀ j, raw17997 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17997step0 = (fun i j => raw17997 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17997step0 raw17997; decide +kernel
      have hl : raw17997step0Labels = raw17997Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17997 raw17997Labels permutation346 hz
    mixedMoment B raw17997step0 raw17997step0Labels = mixedMoment B raw17997step1 raw17997step1Labels := by
      have ha : raw17997step1 = (fun i j => raw17997step0 (permutation57 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17997step1 raw17997step0; decide +kernel
      have hl : raw17997step1Labels = raw17997step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17997step0 raw17997step0Labels permutation57 permutation7
    mixedMoment B raw17997step1 raw17997step1Labels = mixedMoment B raw17997step2 raw17997step2Labels := by
      have ha : raw17997step2 = -raw17997step1 := by apply Matrix.ext; change ∀ i j, raw17997step2 i j = -(raw17997step1 i j); unfold raw17997step2 raw17997step1; decide +kernel
      have hl : raw17997step2Labels = raw17997step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17997step2 raw17997step2Labels = mixedMoment B raw17997step3 raw17997step3Labels := by
      have ha : raw17997step3 = raw17997step2 := by apply Matrix.ext; unfold raw17997step3 raw17997step2; decide +kernel
      have hl : raw17997step2Labels = labelEmbedding10 ∘ raw17997step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17997step2 raw17997step2Labels raw17997step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5473 node5473Labels := by rfl

def raw17998 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw17998Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17998step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw17998step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17998step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![2, 0, -2], ![2, -1, -1]]
def raw17998step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17998step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw17998step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17998step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw17998step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17998 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17998 raw17998Labels = mixedMoment B node5207 node5207Labels := by
  calc
    mixedMoment B raw17998 raw17998Labels = mixedMoment B raw17998step0 raw17998step0Labels := by
      have hz : ∀ j, raw17998 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17998step0 = (fun i j => raw17998 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17998step0 raw17998; decide +kernel
      have hl : raw17998step0Labels = raw17998Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17998 raw17998Labels permutation434 hz
    mixedMoment B raw17998step0 raw17998step0Labels = mixedMoment B raw17998step1 raw17998step1Labels := by
      have hz : ∀ j, raw17998step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw17998step1 = (fun i j => raw17998step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw17998step1 raw17998step0; decide +kernel
      have hl : raw17998step1Labels = raw17998step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17998step0 raw17998step0Labels permutation80 hz
    mixedMoment B raw17998step1 raw17998step1Labels = mixedMoment B raw17998step2 raw17998step2Labels := by
      have ha : raw17998step2 = (fun i j => raw17998step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17998step2 raw17998step1; decide +kernel
      have hl : raw17998step2Labels = raw17998step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17998step1 raw17998step1Labels permutation8 permutation3
    mixedMoment B raw17998step2 raw17998step2Labels = mixedMoment B raw17998step3 raw17998step3Labels := by
      have ha : raw17998step3 = raw17998step2 := by apply Matrix.ext; unfold raw17998step3 raw17998step2; decide +kernel
      have hl : raw17998step2Labels = labelEmbedding6 ∘ raw17998step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17998step2 raw17998step2Labels raw17998step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5207 node5207Labels := by rfl

def raw17999 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw17999Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17999step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw17999step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17999step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![2, 0, -2], ![2, -1, -1]]
def raw17999step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17999step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw17999step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17999 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17999 raw17999Labels = mixedMoment B node5371 node5371Labels := by
  calc
    mixedMoment B raw17999 raw17999Labels = mixedMoment B raw17999step0 raw17999step0Labels := by
      have hz : ∀ j, raw17999 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17999step0 = (fun i j => raw17999 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17999step0 raw17999; decide +kernel
      have hl : raw17999step0Labels = raw17999Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17999 raw17999Labels permutation434 hz
    mixedMoment B raw17999step0 raw17999step0Labels = mixedMoment B raw17999step1 raw17999step1Labels := by
      have hz : ∀ j, raw17999step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw17999step1 = (fun i j => raw17999step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw17999step1 raw17999step0; decide +kernel
      have hl : raw17999step1Labels = raw17999step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17999step0 raw17999step0Labels permutation80 hz
    mixedMoment B raw17999step1 raw17999step1Labels = mixedMoment B raw17999step2 raw17999step2Labels := by
      have ha : raw17999step2 = (fun i j => raw17999step1 (permutation15 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17999step2 raw17999step1; decide +kernel
      have hl : raw17999step2Labels = raw17999step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17999step1 raw17999step1Labels permutation15 permutation2
    _ = mixedMoment B node5371 node5371Labels := by rfl

def raw18000 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw18000Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18000step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw18000step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18000step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw18000step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18000step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw18000step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18000 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18000 raw18000Labels = mixedMoment B node5368 node5368Labels := by
  calc
    mixedMoment B raw18000 raw18000Labels = mixedMoment B raw18000step0 raw18000step0Labels := by
      have hz : ∀ j, raw18000 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18000step0 = (fun i j => raw18000 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18000step0 raw18000; decide +kernel
      have hl : raw18000step0Labels = raw18000Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18000 raw18000Labels permutation434 hz
    mixedMoment B raw18000step0 raw18000step0Labels = mixedMoment B raw18000step1 raw18000step1Labels := by
      have ha : raw18000step1 = (fun i j => raw18000step0 (permutation127 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18000step1 raw18000step0; decide +kernel
      have hl : raw18000step1Labels = raw18000step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18000step0 raw18000step0Labels permutation127 permutation2
    mixedMoment B raw18000step1 raw18000step1Labels = mixedMoment B raw18000step2 raw18000step2Labels := by
      have ha : raw18000step2 = -raw18000step1 := by apply Matrix.ext; change ∀ i j, raw18000step2 i j = -(raw18000step1 i j); unfold raw18000step2 raw18000step1; decide +kernel
      have hl : raw18000step2Labels = raw18000step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5368 node5368Labels := by rfl

def raw18001 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw18001Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18001step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw18001step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18001step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw18001step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18001step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw18001step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18001 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18001 raw18001Labels = mixedMoment B node5368 node5368Labels := by
  calc
    mixedMoment B raw18001 raw18001Labels = mixedMoment B raw18001step0 raw18001step0Labels := by
      have hz : ∀ j, raw18001 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18001step0 = (fun i j => raw18001 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18001step0 raw18001; decide +kernel
      have hl : raw18001step0Labels = raw18001Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18001 raw18001Labels permutation346 hz
    mixedMoment B raw18001step0 raw18001step0Labels = mixedMoment B raw18001step1 raw18001step1Labels := by
      have ha : raw18001step1 = (fun i j => raw18001step0 (permutation127 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18001step1 raw18001step0; decide +kernel
      have hl : raw18001step1Labels = raw18001step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18001step0 raw18001step0Labels permutation127 permutation2
    mixedMoment B raw18001step1 raw18001step1Labels = mixedMoment B raw18001step2 raw18001step2Labels := by
      have ha : raw18001step2 = -raw18001step1 := by apply Matrix.ext; change ∀ i j, raw18001step2 i j = -(raw18001step1 i j); unfold raw18001step2 raw18001step1; decide +kernel
      have hl : raw18001step2Labels = raw18001step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5368 node5368Labels := by rfl

def raw18002 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw18002Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18002step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw18002step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18002step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![2, 0, -2], ![1, 0, -1]]
def raw18002step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18002step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw18002step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18002step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw18002step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18002 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18002 raw18002Labels = mixedMoment B node5413 node5413Labels := by
  calc
    mixedMoment B raw18002 raw18002Labels = mixedMoment B raw18002step0 raw18002step0Labels := by
      have hz : ∀ j, raw18002 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18002step0 = (fun i j => raw18002 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18002step0 raw18002; decide +kernel
      have hl : raw18002step0Labels = raw18002Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18002 raw18002Labels permutation434 hz
    mixedMoment B raw18002step0 raw18002step0Labels = mixedMoment B raw18002step1 raw18002step1Labels := by
      have hz : ∀ j, raw18002step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw18002step1 = (fun i j => raw18002step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw18002step1 raw18002step0; decide +kernel
      have hl : raw18002step1Labels = raw18002step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18002step0 raw18002step0Labels permutation80 hz
    mixedMoment B raw18002step1 raw18002step1Labels = mixedMoment B raw18002step2 raw18002step2Labels := by
      have ha : raw18002step2 = (fun i j => raw18002step1 (permutation25 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18002step2 raw18002step1; decide +kernel
      have hl : raw18002step2Labels = raw18002step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18002step1 raw18002step1Labels permutation25 permutation2
    mixedMoment B raw18002step2 raw18002step2Labels = mixedMoment B raw18002step3 raw18002step3Labels := by
      have ha : raw18002step3 = -raw18002step2 := by apply Matrix.ext; change ∀ i j, raw18002step3 i j = -(raw18002step2 i j); unfold raw18002step3 raw18002step2; decide +kernel
      have hl : raw18002step3Labels = raw18002step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5413 node5413Labels := by rfl

def raw18003 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw18003Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18003step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw18003step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18003step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 1, -2], ![3, -2, -1]]
def raw18003step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18003step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![3, -1, -2]]
def raw18003step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18003step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![3, -1, -2]]
def raw18003step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18003 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18003 raw18003Labels = mixedMoment B node5201 node5201Labels := by
  calc
    mixedMoment B raw18003 raw18003Labels = mixedMoment B raw18003step0 raw18003step0Labels := by
      have hz : ∀ j, raw18003 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18003step0 = (fun i j => raw18003 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18003step0 raw18003; decide +kernel
      have hl : raw18003step0Labels = raw18003Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18003 raw18003Labels permutation434 hz
    mixedMoment B raw18003step0 raw18003step0Labels = mixedMoment B raw18003step1 raw18003step1Labels := by
      have hz : ∀ j, raw18003step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw18003step1 = (fun i j => raw18003step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw18003step1 raw18003step0; decide +kernel
      have hl : raw18003step1Labels = raw18003step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18003step0 raw18003step0Labels permutation80 hz
    mixedMoment B raw18003step1 raw18003step1Labels = mixedMoment B raw18003step2 raw18003step2Labels := by
      have ha : raw18003step2 = (fun i j => raw18003step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18003step2 raw18003step1; decide +kernel
      have hl : raw18003step2Labels = raw18003step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18003step1 raw18003step1Labels permutation8 permutation3
    mixedMoment B raw18003step2 raw18003step2Labels = mixedMoment B raw18003step3 raw18003step3Labels := by
      have ha : raw18003step3 = raw18003step2 := by apply Matrix.ext; unfold raw18003step3 raw18003step2; decide +kernel
      have hl : raw18003step2Labels = labelEmbedding6 ∘ raw18003step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18003step2 raw18003step2Labels raw18003step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5201 node5201Labels := by rfl

def raw18004 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw18004Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18004step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw18004step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18004step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, 1, -2], ![3, -2, -1]]
def raw18004step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18004step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![-2, 2, 0], ![-2, 1, 1]]
def raw18004step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18004step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw18004step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18004step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw18004step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18004 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18004 raw18004Labels = mixedMoment B node5207 node5207Labels := by
  calc
    mixedMoment B raw18004 raw18004Labels = mixedMoment B raw18004step0 raw18004step0Labels := by
      have hz : ∀ j, raw18004 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18004step0 = (fun i j => raw18004 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18004step0 raw18004; decide +kernel
      have hl : raw18004step0Labels = raw18004Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18004 raw18004Labels permutation434 hz
    mixedMoment B raw18004step0 raw18004step0Labels = mixedMoment B raw18004step1 raw18004step1Labels := by
      have hz : ∀ j, raw18004step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw18004step1 = (fun i j => raw18004step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw18004step1 raw18004step0; decide +kernel
      have hl : raw18004step1Labels = raw18004step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18004step0 raw18004step0Labels permutation80 hz
    mixedMoment B raw18004step1 raw18004step1Labels = mixedMoment B raw18004step2 raw18004step2Labels := by
      have ha : raw18004step2 = (fun i j => raw18004step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18004step2 raw18004step1; decide +kernel
      have hl : raw18004step2Labels = raw18004step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18004step1 raw18004step1Labels permutation31 permutation3
    mixedMoment B raw18004step2 raw18004step2Labels = mixedMoment B raw18004step3 raw18004step3Labels := by
      have ha : raw18004step3 = -raw18004step2 := by apply Matrix.ext; change ∀ i j, raw18004step3 i j = -(raw18004step2 i j); unfold raw18004step3 raw18004step2; decide +kernel
      have hl : raw18004step3Labels = raw18004step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18004step3 raw18004step3Labels = mixedMoment B raw18004step4 raw18004step4Labels := by
      have ha : raw18004step4 = raw18004step3 := by apply Matrix.ext; unfold raw18004step4 raw18004step3; decide +kernel
      have hl : raw18004step3Labels = labelEmbedding6 ∘ raw18004step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18004step3 raw18004step3Labels raw18004step4Labels labelEmbedding6 hl
    _ = mixedMoment B node5207 node5207Labels := by rfl

def raw18005 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw18005Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18005step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw18005step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18005step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw18005step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18005step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw18005step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18005step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw18005step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18005 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18005 raw18005Labels = mixedMoment B node5199 node5199Labels := by
  calc
    mixedMoment B raw18005 raw18005Labels = mixedMoment B raw18005step0 raw18005step0Labels := by
      have hz : ∀ j, raw18005 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18005step0 = (fun i j => raw18005 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18005step0 raw18005; decide +kernel
      have hl : raw18005step0Labels = raw18005Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18005 raw18005Labels permutation434 hz
    mixedMoment B raw18005step0 raw18005step0Labels = mixedMoment B raw18005step1 raw18005step1Labels := by
      have ha : raw18005step1 = (fun i j => raw18005step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18005step1 raw18005step0; decide +kernel
      have hl : raw18005step1Labels = raw18005step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18005step0 raw18005step0Labels permutation149 permutation3
    mixedMoment B raw18005step1 raw18005step1Labels = mixedMoment B raw18005step2 raw18005step2Labels := by
      have ha : raw18005step2 = -raw18005step1 := by apply Matrix.ext; change ∀ i j, raw18005step2 i j = -(raw18005step1 i j); unfold raw18005step2 raw18005step1; decide +kernel
      have hl : raw18005step2Labels = raw18005step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18005step2 raw18005step2Labels = mixedMoment B raw18005step3 raw18005step3Labels := by
      have ha : raw18005step3 = raw18005step2 := by apply Matrix.ext; unfold raw18005step3 raw18005step2; decide +kernel
      have hl : raw18005step2Labels = labelEmbedding6 ∘ raw18005step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18005step2 raw18005step2Labels raw18005step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5199 node5199Labels := by rfl

def raw18006 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw18006Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18006step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw18006step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18006step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw18006step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18006step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw18006step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18006step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw18006step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18006 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18006 raw18006Labels = mixedMoment B node5199 node5199Labels := by
  calc
    mixedMoment B raw18006 raw18006Labels = mixedMoment B raw18006step0 raw18006step0Labels := by
      have hz : ∀ j, raw18006 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18006step0 = (fun i j => raw18006 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18006step0 raw18006; decide +kernel
      have hl : raw18006step0Labels = raw18006Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18006 raw18006Labels permutation346 hz
    mixedMoment B raw18006step0 raw18006step0Labels = mixedMoment B raw18006step1 raw18006step1Labels := by
      have ha : raw18006step1 = (fun i j => raw18006step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18006step1 raw18006step0; decide +kernel
      have hl : raw18006step1Labels = raw18006step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18006step0 raw18006step0Labels permutation149 permutation3
    mixedMoment B raw18006step1 raw18006step1Labels = mixedMoment B raw18006step2 raw18006step2Labels := by
      have ha : raw18006step2 = -raw18006step1 := by apply Matrix.ext; change ∀ i j, raw18006step2 i j = -(raw18006step1 i j); unfold raw18006step2 raw18006step1; decide +kernel
      have hl : raw18006step2Labels = raw18006step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18006step2 raw18006step2Labels = mixedMoment B raw18006step3 raw18006step3Labels := by
      have ha : raw18006step3 = raw18006step2 := by apply Matrix.ext; unfold raw18006step3 raw18006step2; decide +kernel
      have hl : raw18006step2Labels = labelEmbedding6 ∘ raw18006step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18006step2 raw18006step2Labels raw18006step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5199 node5199Labels := by rfl

def raw18007 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![3, -2, -1]]
def raw18007Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18007step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 2, -2], ![3, -2, -1]]
def raw18007step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18007step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 2, -2], ![3, -2, -1]]
def raw18007step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18007step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 2, -1], ![-2, 1, 1]]
def raw18007step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18007step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw18007step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18007step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw18007step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18007 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18007 raw18007Labels = mixedMoment B node5300 node5300Labels := by
  calc
    mixedMoment B raw18007 raw18007Labels = mixedMoment B raw18007step0 raw18007step0Labels := by
      have hz : ∀ j, raw18007 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18007step0 = (fun i j => raw18007 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18007step0 raw18007; decide +kernel
      have hl : raw18007step0Labels = raw18007Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18007 raw18007Labels permutation434 hz
    mixedMoment B raw18007step0 raw18007step0Labels = mixedMoment B raw18007step1 raw18007step1Labels := by
      have hz : ∀ j, raw18007step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw18007step1 = (fun i j => raw18007step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw18007step1 raw18007step0; decide +kernel
      have hl : raw18007step1Labels = raw18007step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18007step0 raw18007step0Labels permutation80 hz
    mixedMoment B raw18007step1 raw18007step1Labels = mixedMoment B raw18007step2 raw18007step2Labels := by
      have ha : raw18007step2 = (fun i j => raw18007step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18007step2 raw18007step1; decide +kernel
      have hl : raw18007step2Labels = raw18007step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18007step1 raw18007step1Labels permutation31 permutation3
    mixedMoment B raw18007step2 raw18007step2Labels = mixedMoment B raw18007step3 raw18007step3Labels := by
      have ha : raw18007step3 = -raw18007step2 := by apply Matrix.ext; change ∀ i j, raw18007step3 i j = -(raw18007step2 i j); unfold raw18007step3 raw18007step2; decide +kernel
      have hl : raw18007step3Labels = raw18007step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18007step3 raw18007step3Labels = mixedMoment B raw18007step4 raw18007step4Labels := by
      have ha : raw18007step4 = raw18007step3 := by apply Matrix.ext; unfold raw18007step4 raw18007step3; decide +kernel
      have hl : raw18007step3Labels = labelEmbedding6 ∘ raw18007step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18007step3 raw18007step3Labels raw18007step4Labels labelEmbedding6 hl
    _ = mixedMoment B node5300 node5300Labels := by rfl

def raw18008 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw18008Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18008step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw18008step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18008step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![1, 1, -2], ![2, -1, -1]]
def raw18008step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18008step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw18008step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18008step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw18008step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18008step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw18008step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18008 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18008 raw18008Labels = mixedMoment B node3817 node3817Labels := by
  calc
    mixedMoment B raw18008 raw18008Labels = mixedMoment B raw18008step0 raw18008step0Labels := by
      have hz : ∀ j, raw18008 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18008step0 = (fun i j => raw18008 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18008step0 raw18008; decide +kernel
      have hl : raw18008step0Labels = raw18008Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18008 raw18008Labels permutation434 hz
    mixedMoment B raw18008step0 raw18008step0Labels = mixedMoment B raw18008step1 raw18008step1Labels := by
      have hz : ∀ j, raw18008step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw18008step1 = (fun i j => raw18008step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw18008step1 raw18008step0; decide +kernel
      have hl : raw18008step1Labels = raw18008step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18008step0 raw18008step0Labels permutation80 hz
    mixedMoment B raw18008step1 raw18008step1Labels = mixedMoment B raw18008step2 raw18008step2Labels := by
      have ha : raw18008step2 = (fun i j => raw18008step1 (permutation15 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18008step2 raw18008step1; decide +kernel
      have hl : raw18008step2Labels = raw18008step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18008step1 raw18008step1Labels permutation15 permutation7
    mixedMoment B raw18008step2 raw18008step2Labels = mixedMoment B raw18008step3 raw18008step3Labels := by
      have ha : raw18008step3 = -raw18008step2 := by apply Matrix.ext; change ∀ i j, raw18008step3 i j = -(raw18008step2 i j); unfold raw18008step3 raw18008step2; decide +kernel
      have hl : raw18008step3Labels = raw18008step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18008step3 raw18008step3Labels = mixedMoment B raw18008step4 raw18008step4Labels := by
      have ha : raw18008step4 = raw18008step3 := by apply Matrix.ext; unfold raw18008step4 raw18008step3; decide +kernel
      have hl : raw18008step3Labels = labelEmbedding1 ∘ raw18008step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18008step3 raw18008step3Labels raw18008step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3817 node3817Labels := by rfl

def raw18009 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw18009Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18009step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw18009step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18009step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18009step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18009step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18009step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18009 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18009 raw18009Labels = mixedMoment B node3958 node3958Labels := by
  calc
    mixedMoment B raw18009 raw18009Labels = mixedMoment B raw18009step0 raw18009step0Labels := by
      have hz : ∀ j, raw18009 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18009step0 = (fun i j => raw18009 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18009step0 raw18009; decide +kernel
      have hl : raw18009step0Labels = raw18009Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18009 raw18009Labels permutation434 hz
    mixedMoment B raw18009step0 raw18009step0Labels = mixedMoment B raw18009step1 raw18009step1Labels := by
      have ha : raw18009step1 = (fun i j => raw18009step0 (permutation126 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18009step1 raw18009step0; decide +kernel
      have hl : raw18009step1Labels = raw18009step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18009step0 raw18009step0Labels permutation126 permutation7
    mixedMoment B raw18009step1 raw18009step1Labels = mixedMoment B raw18009step2 raw18009step2Labels := by
      have ha : raw18009step2 = raw18009step1 := by apply Matrix.ext; unfold raw18009step2 raw18009step1; decide +kernel
      have hl : raw18009step1Labels = labelEmbedding1 ∘ raw18009step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18009step1 raw18009step1Labels raw18009step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3958 node3958Labels := by rfl

def raw18010 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw18010Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18010step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw18010step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18010step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18010step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18010step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18010step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18010 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18010 raw18010Labels = mixedMoment B node3958 node3958Labels := by
  calc
    mixedMoment B raw18010 raw18010Labels = mixedMoment B raw18010step0 raw18010step0Labels := by
      have hz : ∀ j, raw18010 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18010step0 = (fun i j => raw18010 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18010step0 raw18010; decide +kernel
      have hl : raw18010step0Labels = raw18010Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18010 raw18010Labels permutation346 hz
    mixedMoment B raw18010step0 raw18010step0Labels = mixedMoment B raw18010step1 raw18010step1Labels := by
      have ha : raw18010step1 = (fun i j => raw18010step0 (permutation126 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18010step1 raw18010step0; decide +kernel
      have hl : raw18010step1Labels = raw18010step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18010step0 raw18010step0Labels permutation126 permutation7
    mixedMoment B raw18010step1 raw18010step1Labels = mixedMoment B raw18010step2 raw18010step2Labels := by
      have ha : raw18010step2 = raw18010step1 := by apply Matrix.ext; unfold raw18010step2 raw18010step1; decide +kernel
      have hl : raw18010step1Labels = labelEmbedding1 ∘ raw18010step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18010step1 raw18010step1Labels raw18010step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3958 node3958Labels := by rfl

def raw18011 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![2, -1, -1]]
def raw18011Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18011step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 2, -2], ![2, -1, -1]]
def raw18011step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18011step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 2, -2], ![2, -1, -1]]
def raw18011step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18011step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![-1, -1, 2], ![-2, 2, 0]]
def raw18011step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18011step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0]]
def raw18011step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18011step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0]]
def raw18011step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18011 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18011 raw18011Labels = mixedMoment B node3987 node3987Labels := by
  calc
    mixedMoment B raw18011 raw18011Labels = mixedMoment B raw18011step0 raw18011step0Labels := by
      have hz : ∀ j, raw18011 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18011step0 = (fun i j => raw18011 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18011step0 raw18011; decide +kernel
      have hl : raw18011step0Labels = raw18011Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18011 raw18011Labels permutation434 hz
    mixedMoment B raw18011step0 raw18011step0Labels = mixedMoment B raw18011step1 raw18011step1Labels := by
      have hz : ∀ j, raw18011step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw18011step1 = (fun i j => raw18011step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw18011step1 raw18011step0; decide +kernel
      have hl : raw18011step1Labels = raw18011step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18011step0 raw18011step0Labels permutation80 hz
    mixedMoment B raw18011step1 raw18011step1Labels = mixedMoment B raw18011step2 raw18011step2Labels := by
      have ha : raw18011step2 = (fun i j => raw18011step1 (permutation15 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18011step2 raw18011step1; decide +kernel
      have hl : raw18011step2Labels = raw18011step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18011step1 raw18011step1Labels permutation15 permutation7
    mixedMoment B raw18011step2 raw18011step2Labels = mixedMoment B raw18011step3 raw18011step3Labels := by
      have ha : raw18011step3 = -raw18011step2 := by apply Matrix.ext; change ∀ i j, raw18011step3 i j = -(raw18011step2 i j); unfold raw18011step3 raw18011step2; decide +kernel
      have hl : raw18011step3Labels = raw18011step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18011step3 raw18011step3Labels = mixedMoment B raw18011step4 raw18011step4Labels := by
      have ha : raw18011step4 = raw18011step3 := by apply Matrix.ext; unfold raw18011step4 raw18011step3; decide +kernel
      have hl : raw18011step3Labels = labelEmbedding1 ∘ raw18011step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18011step3 raw18011step3Labels raw18011step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3987 node3987Labels := by rfl

def raw18012 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1]]
def raw18012Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18012step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1]]
def raw18012step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18012step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![1, 1, -2], ![1, 0, -1]]
def raw18012step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18012step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw18012step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18012step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw18012step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18012 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18012 raw18012Labels = mixedMoment B node3986 node3986Labels := by
  calc
    mixedMoment B raw18012 raw18012Labels = mixedMoment B raw18012step0 raw18012step0Labels := by
      have hz : ∀ j, raw18012 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18012step0 = (fun i j => raw18012 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18012step0 raw18012; decide +kernel
      have hl : raw18012step0Labels = raw18012Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18012 raw18012Labels permutation434 hz
    mixedMoment B raw18012step0 raw18012step0Labels = mixedMoment B raw18012step1 raw18012step1Labels := by
      have hz : ∀ j, raw18012step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw18012step1 = (fun i j => raw18012step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw18012step1 raw18012step0; decide +kernel
      have hl : raw18012step1Labels = raw18012step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18012step0 raw18012step0Labels permutation80 hz
    mixedMoment B raw18012step1 raw18012step1Labels = mixedMoment B raw18012step2 raw18012step2Labels := by
      have ha : raw18012step2 = (fun i j => raw18012step1 (permutation24 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18012step2 raw18012step1; decide +kernel
      have hl : raw18012step2Labels = raw18012step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18012step1 raw18012step1Labels permutation24 permutation7
    mixedMoment B raw18012step2 raw18012step2Labels = mixedMoment B raw18012step3 raw18012step3Labels := by
      have ha : raw18012step3 = raw18012step2 := by apply Matrix.ext; unfold raw18012step3 raw18012step2; decide +kernel
      have hl : raw18012step2Labels = labelEmbedding1 ∘ raw18012step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18012step2 raw18012step2Labels raw18012step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3986 node3986Labels := by rfl

def raw18013 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw18013Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18013step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw18013step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18013step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw18013step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18013step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw18013step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18013step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18013step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18013step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18013step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18013 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18013 raw18013Labels = mixedMoment B node3584 node3584Labels := by
  calc
    mixedMoment B raw18013 raw18013Labels = mixedMoment B raw18013step0 raw18013step0Labels := by
      have hz : ∀ j, raw18013 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18013step0 = (fun i j => raw18013 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18013step0 raw18013; decide +kernel
      have hl : raw18013step0Labels = raw18013Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18013 raw18013Labels permutation434 hz
    mixedMoment B raw18013step0 raw18013step0Labels = mixedMoment B raw18013step1 raw18013step1Labels := by
      have hz : ∀ j, raw18013step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw18013step1 = (fun i j => raw18013step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw18013step1 raw18013step0; decide +kernel
      have hl : raw18013step1Labels = raw18013step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18013step0 raw18013step0Labels permutation80 hz
    mixedMoment B raw18013step1 raw18013step1Labels = mixedMoment B raw18013step2 raw18013step2Labels := by
      have ha : raw18013step2 = (fun i j => raw18013step1 (permutation11 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18013step2 raw18013step1; decide +kernel
      have hl : raw18013step2Labels = raw18013step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18013step1 raw18013step1Labels permutation11 permutation5
    mixedMoment B raw18013step2 raw18013step2Labels = mixedMoment B raw18013step3 raw18013step3Labels := by
      have ha : raw18013step3 = -raw18013step2 := by apply Matrix.ext; change ∀ i j, raw18013step3 i j = -(raw18013step2 i j); unfold raw18013step3 raw18013step2; decide +kernel
      have hl : raw18013step3Labels = raw18013step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18013step3 raw18013step3Labels = mixedMoment B raw18013step4 raw18013step4Labels := by
      have ha : raw18013step4 = raw18013step3 := by apply Matrix.ext; unfold raw18013step4 raw18013step3; decide +kernel
      have hl : raw18013step3Labels = labelEmbedding1 ∘ raw18013step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18013step3 raw18013step3Labels raw18013step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3584 node3584Labels := by rfl

def raw18014 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw18014Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18014step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw18014step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18014step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18014step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18014step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18014step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18014 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18014 raw18014Labels = mixedMoment B node3959 node3959Labels := by
  calc
    mixedMoment B raw18014 raw18014Labels = mixedMoment B raw18014step0 raw18014step0Labels := by
      have hz : ∀ j, raw18014 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18014step0 = (fun i j => raw18014 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18014step0 raw18014; decide +kernel
      have hl : raw18014step0Labels = raw18014Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18014 raw18014Labels permutation434 hz
    mixedMoment B raw18014step0 raw18014step0Labels = mixedMoment B raw18014step1 raw18014step1Labels := by
      have ha : raw18014step1 = (fun i j => raw18014step0 (permutation126 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18014step1 raw18014step0; decide +kernel
      have hl : raw18014step1Labels = raw18014step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18014step0 raw18014step0Labels permutation126 permutation7
    mixedMoment B raw18014step1 raw18014step1Labels = mixedMoment B raw18014step2 raw18014step2Labels := by
      have ha : raw18014step2 = raw18014step1 := by apply Matrix.ext; unfold raw18014step2 raw18014step1; decide +kernel
      have hl : raw18014step1Labels = labelEmbedding1 ∘ raw18014step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18014step1 raw18014step1Labels raw18014step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3959 node3959Labels := by rfl

def raw18015 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw18015Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18015step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw18015step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18015step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18015step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18015step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18015step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18015 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18015 raw18015Labels = mixedMoment B node3959 node3959Labels := by
  calc
    mixedMoment B raw18015 raw18015Labels = mixedMoment B raw18015step0 raw18015step0Labels := by
      have hz : ∀ j, raw18015 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18015step0 = (fun i j => raw18015 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18015step0 raw18015; decide +kernel
      have hl : raw18015step0Labels = raw18015Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18015 raw18015Labels permutation346 hz
    mixedMoment B raw18015step0 raw18015step0Labels = mixedMoment B raw18015step1 raw18015step1Labels := by
      have ha : raw18015step1 = (fun i j => raw18015step0 (permutation126 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18015step1 raw18015step0; decide +kernel
      have hl : raw18015step1Labels = raw18015step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18015step0 raw18015step0Labels permutation126 permutation7
    mixedMoment B raw18015step1 raw18015step1Labels = mixedMoment B raw18015step2 raw18015step2Labels := by
      have ha : raw18015step2 = raw18015step1 := by apply Matrix.ext; unfold raw18015step2 raw18015step1; decide +kernel
      have hl : raw18015step1Labels = labelEmbedding1 ∘ raw18015step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18015step1 raw18015step1Labels raw18015step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3959 node3959Labels := by rfl

def raw18016 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![2, -1, -1]]
def raw18016Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18016step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 0, 0], ![0, 2, -2], ![2, -1, -1]]
def raw18016step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18016step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 2, -2], ![2, -1, -1]]
def raw18016step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18016step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw18016step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18016step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw18016step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18016 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18016 raw18016Labels = mixedMoment B node4030 node4030Labels := by
  calc
    mixedMoment B raw18016 raw18016Labels = mixedMoment B raw18016step0 raw18016step0Labels := by
      have hz : ∀ j, raw18016 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18016step0 = (fun i j => raw18016 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18016step0 raw18016; decide +kernel
      have hl : raw18016step0Labels = raw18016Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18016 raw18016Labels permutation434 hz
    mixedMoment B raw18016step0 raw18016step0Labels = mixedMoment B raw18016step1 raw18016step1Labels := by
      have hz : ∀ j, raw18016step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw18016step1 = (fun i j => raw18016step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw18016step1 raw18016step0; decide +kernel
      have hl : raw18016step1Labels = raw18016step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18016step0 raw18016step0Labels permutation80 hz
    mixedMoment B raw18016step1 raw18016step1Labels = mixedMoment B raw18016step2 raw18016step2Labels := by
      have ha : raw18016step2 = (fun i j => raw18016step1 (permutation18 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18016step2 raw18016step1; decide +kernel
      have hl : raw18016step2Labels = raw18016step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18016step1 raw18016step1Labels permutation18 permutation5
    mixedMoment B raw18016step2 raw18016step2Labels = mixedMoment B raw18016step3 raw18016step3Labels := by
      have ha : raw18016step3 = raw18016step2 := by apply Matrix.ext; unfold raw18016step3 raw18016step2; decide +kernel
      have hl : raw18016step2Labels = labelEmbedding1 ∘ raw18016step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18016step2 raw18016step2Labels raw18016step3Labels labelEmbedding1 hl
    _ = mixedMoment B node4030 node4030Labels := by rfl

def raw18017 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1]]
def raw18017Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18017step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1]]
def raw18017step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18017step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1]]
def raw18017step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18017step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0]]
def raw18017step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18017step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0]]
def raw18017step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18017 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18017 raw18017Labels = mixedMoment B node3987 node3987Labels := by
  calc
    mixedMoment B raw18017 raw18017Labels = mixedMoment B raw18017step0 raw18017step0Labels := by
      have hz : ∀ j, raw18017 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18017step0 = (fun i j => raw18017 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18017step0 raw18017; decide +kernel
      have hl : raw18017step0Labels = raw18017Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18017 raw18017Labels permutation434 hz
    mixedMoment B raw18017step0 raw18017step0Labels = mixedMoment B raw18017step1 raw18017step1Labels := by
      have hz : ∀ j, raw18017step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw18017step1 = (fun i j => raw18017step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw18017step1 raw18017step0; decide +kernel
      have hl : raw18017step1Labels = raw18017step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18017step0 raw18017step0Labels permutation80 hz
    mixedMoment B raw18017step1 raw18017step1Labels = mixedMoment B raw18017step2 raw18017step2Labels := by
      have ha : raw18017step2 = (fun i j => raw18017step1 (permutation24 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18017step2 raw18017step1; decide +kernel
      have hl : raw18017step2Labels = raw18017step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18017step1 raw18017step1Labels permutation24 permutation7
    mixedMoment B raw18017step2 raw18017step2Labels = mixedMoment B raw18017step3 raw18017step3Labels := by
      have ha : raw18017step3 = raw18017step2 := by apply Matrix.ext; unfold raw18017step3 raw18017step2; decide +kernel
      have hl : raw18017step2Labels = labelEmbedding1 ∘ raw18017step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18017step2 raw18017step2Labels raw18017step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3987 node3987Labels := by rfl

def raw18018 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw18018Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18018step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw18018step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18018step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw18018step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18018step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18018step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18018step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18018step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18018 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18018 raw18018Labels = mixedMoment B node3578 node3578Labels := by
  calc
    mixedMoment B raw18018 raw18018Labels = mixedMoment B raw18018step0 raw18018step0Labels := by
      have hz : ∀ j, raw18018 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18018step0 = (fun i j => raw18018 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18018step0 raw18018; decide +kernel
      have hl : raw18018step0Labels = raw18018Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18018 raw18018Labels permutation434 hz
    mixedMoment B raw18018step0 raw18018step0Labels = mixedMoment B raw18018step1 raw18018step1Labels := by
      have ha : raw18018step1 = (fun i j => raw18018step0 (permutation44 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18018step1 raw18018step0; decide +kernel
      have hl : raw18018step1Labels = raw18018step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18018step0 raw18018step0Labels permutation44 permutation5
    mixedMoment B raw18018step1 raw18018step1Labels = mixedMoment B raw18018step2 raw18018step2Labels := by
      have ha : raw18018step2 = -raw18018step1 := by apply Matrix.ext; change ∀ i j, raw18018step2 i j = -(raw18018step1 i j); unfold raw18018step2 raw18018step1; decide +kernel
      have hl : raw18018step2Labels = raw18018step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18018step2 raw18018step2Labels = mixedMoment B raw18018step3 raw18018step3Labels := by
      have ha : raw18018step3 = raw18018step2 := by apply Matrix.ext; unfold raw18018step3 raw18018step2; decide +kernel
      have hl : raw18018step2Labels = labelEmbedding1 ∘ raw18018step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18018step2 raw18018step2Labels raw18018step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3578 node3578Labels := by rfl

def raw18019 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw18019Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18019step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw18019step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18019step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw18019step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18019step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw18019step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18019step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw18019step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18019 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18019 raw18019Labels = mixedMoment B node3767 node3767Labels := by
  calc
    mixedMoment B raw18019 raw18019Labels = mixedMoment B raw18019step0 raw18019step0Labels := by
      have hz : ∀ j, raw18019 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18019step0 = (fun i j => raw18019 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18019step0 raw18019; decide +kernel
      have hl : raw18019step0Labels = raw18019Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18019 raw18019Labels permutation434 hz
    mixedMoment B raw18019step0 raw18019step0Labels = mixedMoment B raw18019step1 raw18019step1Labels := by
      have ha : raw18019step1 = (fun i j => raw18019step0 (permutation57 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18019step1 raw18019step0; decide +kernel
      have hl : raw18019step1Labels = raw18019step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18019step0 raw18019step0Labels permutation57 permutation7
    mixedMoment B raw18019step1 raw18019step1Labels = mixedMoment B raw18019step2 raw18019step2Labels := by
      have ha : raw18019step2 = -raw18019step1 := by apply Matrix.ext; change ∀ i j, raw18019step2 i j = -(raw18019step1 i j); unfold raw18019step2 raw18019step1; decide +kernel
      have hl : raw18019step2Labels = raw18019step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18019step2 raw18019step2Labels = mixedMoment B raw18019step3 raw18019step3Labels := by
      have ha : raw18019step3 = raw18019step2 := by apply Matrix.ext; unfold raw18019step3 raw18019step2; decide +kernel
      have hl : raw18019step2Labels = labelEmbedding1 ∘ raw18019step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18019step2 raw18019step2Labels raw18019step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3767 node3767Labels := by rfl

def raw18020 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw18020Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18020step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw18020step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18020step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw18020step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18020 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18020 raw18020Labels = mixedMoment B node3950 node3950Labels := by
  calc
    mixedMoment B raw18020 raw18020Labels = mixedMoment B raw18020step0 raw18020step0Labels := by
      have ha : raw18020step0 = (fun i j => raw18020 (permutation583 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18020step0 raw18020; decide +kernel
      have hl : raw18020step0Labels = raw18020Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18020 raw18020Labels permutation583 permutation7
    mixedMoment B raw18020step0 raw18020step0Labels = mixedMoment B raw18020step1 raw18020step1Labels := by
      have ha : raw18020step1 = raw18020step0 := by apply Matrix.ext; unfold raw18020step1 raw18020step0; decide +kernel
      have hl : raw18020step0Labels = labelEmbedding1 ∘ raw18020step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18020step0 raw18020step0Labels raw18020step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3950 node3950Labels := by rfl

def raw18021 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 2, -2], ![2, -1, -1]]
def raw18021Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18021step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![0, 2, -2], ![2, -1, -1]]
def raw18021step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18021step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw18021step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18021step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18021step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18021step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18021step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18021 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18021 raw18021Labels = mixedMoment B node3959 node3959Labels := by
  calc
    mixedMoment B raw18021 raw18021Labels = mixedMoment B raw18021step0 raw18021step0Labels := by
      have hz : ∀ j, raw18021 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18021step0 = (fun i j => raw18021 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18021step0 raw18021; decide +kernel
      have hl : raw18021step0Labels = raw18021Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18021 raw18021Labels permutation434 hz
    mixedMoment B raw18021step0 raw18021step0Labels = mixedMoment B raw18021step1 raw18021step1Labels := by
      have ha : raw18021step1 = (fun i j => raw18021step0 (permutation57 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18021step1 raw18021step0; decide +kernel
      have hl : raw18021step1Labels = raw18021step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18021step0 raw18021step0Labels permutation57 permutation7
    mixedMoment B raw18021step1 raw18021step1Labels = mixedMoment B raw18021step2 raw18021step2Labels := by
      have ha : raw18021step2 = -raw18021step1 := by apply Matrix.ext; change ∀ i j, raw18021step2 i j = -(raw18021step1 i j); unfold raw18021step2 raw18021step1; decide +kernel
      have hl : raw18021step2Labels = raw18021step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18021step2 raw18021step2Labels = mixedMoment B raw18021step3 raw18021step3Labels := by
      have ha : raw18021step3 = raw18021step2 := by apply Matrix.ext; unfold raw18021step3 raw18021step2; decide +kernel
      have hl : raw18021step2Labels = labelEmbedding1 ∘ raw18021step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18021step2 raw18021step2Labels raw18021step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3959 node3959Labels := by rfl

def raw18022 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1]]
def raw18022Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18022step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1]]
def raw18022step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18022step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw18022step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18022step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18022step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18022step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18022step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18022 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18022 raw18022Labels = mixedMoment B node3958 node3958Labels := by
  calc
    mixedMoment B raw18022 raw18022Labels = mixedMoment B raw18022step0 raw18022step0Labels := by
      have hz : ∀ j, raw18022 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18022step0 = (fun i j => raw18022 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18022step0 raw18022; decide +kernel
      have hl : raw18022step0Labels = raw18022Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18022 raw18022Labels permutation434 hz
    mixedMoment B raw18022step0 raw18022step0Labels = mixedMoment B raw18022step1 raw18022step1Labels := by
      have ha : raw18022step1 = (fun i j => raw18022step0 (permutation57 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18022step1 raw18022step0; decide +kernel
      have hl : raw18022step1Labels = raw18022step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18022step0 raw18022step0Labels permutation57 permutation7
    mixedMoment B raw18022step1 raw18022step1Labels = mixedMoment B raw18022step2 raw18022step2Labels := by
      have ha : raw18022step2 = -raw18022step1 := by apply Matrix.ext; change ∀ i j, raw18022step2 i j = -(raw18022step1 i j); unfold raw18022step2 raw18022step1; decide +kernel
      have hl : raw18022step2Labels = raw18022step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18022step2 raw18022step2Labels = mixedMoment B raw18022step3 raw18022step3Labels := by
      have ha : raw18022step3 = raw18022step2 := by apply Matrix.ext; unfold raw18022step3 raw18022step2; decide +kernel
      have hl : raw18022step2Labels = labelEmbedding1 ∘ raw18022step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18022step2 raw18022step2Labels raw18022step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3958 node3958Labels := by rfl

def raw18023 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw18023Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18023step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw18023step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18023step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw18023step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18023step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18023step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18023step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18023step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18023 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18023 raw18023Labels = mixedMoment B node3578 node3578Labels := by
  calc
    mixedMoment B raw18023 raw18023Labels = mixedMoment B raw18023step0 raw18023step0Labels := by
      have hz : ∀ j, raw18023 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18023step0 = (fun i j => raw18023 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18023step0 raw18023; decide +kernel
      have hl : raw18023step0Labels = raw18023Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18023 raw18023Labels permutation346 hz
    mixedMoment B raw18023step0 raw18023step0Labels = mixedMoment B raw18023step1 raw18023step1Labels := by
      have ha : raw18023step1 = (fun i j => raw18023step0 (permutation44 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18023step1 raw18023step0; decide +kernel
      have hl : raw18023step1Labels = raw18023step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18023step0 raw18023step0Labels permutation44 permutation5
    mixedMoment B raw18023step1 raw18023step1Labels = mixedMoment B raw18023step2 raw18023step2Labels := by
      have ha : raw18023step2 = -raw18023step1 := by apply Matrix.ext; change ∀ i j, raw18023step2 i j = -(raw18023step1 i j); unfold raw18023step2 raw18023step1; decide +kernel
      have hl : raw18023step2Labels = raw18023step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18023step2 raw18023step2Labels = mixedMoment B raw18023step3 raw18023step3Labels := by
      have ha : raw18023step3 = raw18023step2 := by apply Matrix.ext; unfold raw18023step3 raw18023step2; decide +kernel
      have hl : raw18023step2Labels = labelEmbedding1 ∘ raw18023step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18023step2 raw18023step2Labels raw18023step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3578 node3578Labels := by rfl

def raw18024 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw18024Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18024step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw18024step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18024step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw18024step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18024step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw18024step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18024step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw18024step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18024 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18024 raw18024Labels = mixedMoment B node3767 node3767Labels := by
  calc
    mixedMoment B raw18024 raw18024Labels = mixedMoment B raw18024step0 raw18024step0Labels := by
      have hz : ∀ j, raw18024 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18024step0 = (fun i j => raw18024 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18024step0 raw18024; decide +kernel
      have hl : raw18024step0Labels = raw18024Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18024 raw18024Labels permutation346 hz
    mixedMoment B raw18024step0 raw18024step0Labels = mixedMoment B raw18024step1 raw18024step1Labels := by
      have ha : raw18024step1 = (fun i j => raw18024step0 (permutation57 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18024step1 raw18024step0; decide +kernel
      have hl : raw18024step1Labels = raw18024step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18024step0 raw18024step0Labels permutation57 permutation7
    mixedMoment B raw18024step1 raw18024step1Labels = mixedMoment B raw18024step2 raw18024step2Labels := by
      have ha : raw18024step2 = -raw18024step1 := by apply Matrix.ext; change ∀ i j, raw18024step2 i j = -(raw18024step1 i j); unfold raw18024step2 raw18024step1; decide +kernel
      have hl : raw18024step2Labels = raw18024step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18024step2 raw18024step2Labels = mixedMoment B raw18024step3 raw18024step3Labels := by
      have ha : raw18024step3 = raw18024step2 := by apply Matrix.ext; unfold raw18024step3 raw18024step2; decide +kernel
      have hl : raw18024step2Labels = labelEmbedding1 ∘ raw18024step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18024step2 raw18024step2Labels raw18024step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3767 node3767Labels := by rfl

def raw18025 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw18025Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18025step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw18025step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18025step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw18025step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18025 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18025 raw18025Labels = mixedMoment B node3950 node3950Labels := by
  calc
    mixedMoment B raw18025 raw18025Labels = mixedMoment B raw18025step0 raw18025step0Labels := by
      have ha : raw18025step0 = (fun i j => raw18025 (permutation588 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18025step0 raw18025; decide +kernel
      have hl : raw18025step0Labels = raw18025Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18025 raw18025Labels permutation588 permutation7
    mixedMoment B raw18025step0 raw18025step0Labels = mixedMoment B raw18025step1 raw18025step1Labels := by
      have ha : raw18025step1 = raw18025step0 := by apply Matrix.ext; unfold raw18025step1 raw18025step0; decide +kernel
      have hl : raw18025step0Labels = labelEmbedding1 ∘ raw18025step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18025step0 raw18025step0Labels raw18025step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3950 node3950Labels := by rfl

def raw18026 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![2, -1, -1]]
def raw18026Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18026step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![0, 2, -2], ![2, -1, -1]]
def raw18026step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18026step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw18026step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18026step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18026step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18026step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18026step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18026 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18026 raw18026Labels = mixedMoment B node3959 node3959Labels := by
  calc
    mixedMoment B raw18026 raw18026Labels = mixedMoment B raw18026step0 raw18026step0Labels := by
      have hz : ∀ j, raw18026 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18026step0 = (fun i j => raw18026 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18026step0 raw18026; decide +kernel
      have hl : raw18026step0Labels = raw18026Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18026 raw18026Labels permutation346 hz
    mixedMoment B raw18026step0 raw18026step0Labels = mixedMoment B raw18026step1 raw18026step1Labels := by
      have ha : raw18026step1 = (fun i j => raw18026step0 (permutation57 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18026step1 raw18026step0; decide +kernel
      have hl : raw18026step1Labels = raw18026step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18026step0 raw18026step0Labels permutation57 permutation7
    mixedMoment B raw18026step1 raw18026step1Labels = mixedMoment B raw18026step2 raw18026step2Labels := by
      have ha : raw18026step2 = -raw18026step1 := by apply Matrix.ext; change ∀ i j, raw18026step2 i j = -(raw18026step1 i j); unfold raw18026step2 raw18026step1; decide +kernel
      have hl : raw18026step2Labels = raw18026step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18026step2 raw18026step2Labels = mixedMoment B raw18026step3 raw18026step3Labels := by
      have ha : raw18026step3 = raw18026step2 := by apply Matrix.ext; unfold raw18026step3 raw18026step2; decide +kernel
      have hl : raw18026step2Labels = labelEmbedding1 ∘ raw18026step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18026step2 raw18026step2Labels raw18026step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3959 node3959Labels := by rfl

def raw18027 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1]]
def raw18027Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18027step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1]]
def raw18027step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18027step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw18027step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18027step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18027step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18027step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18027step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18027 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18027 raw18027Labels = mixedMoment B node3958 node3958Labels := by
  calc
    mixedMoment B raw18027 raw18027Labels = mixedMoment B raw18027step0 raw18027step0Labels := by
      have hz : ∀ j, raw18027 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18027step0 = (fun i j => raw18027 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18027step0 raw18027; decide +kernel
      have hl : raw18027step0Labels = raw18027Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18027 raw18027Labels permutation346 hz
    mixedMoment B raw18027step0 raw18027step0Labels = mixedMoment B raw18027step1 raw18027step1Labels := by
      have ha : raw18027step1 = (fun i j => raw18027step0 (permutation57 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18027step1 raw18027step0; decide +kernel
      have hl : raw18027step1Labels = raw18027step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18027step0 raw18027step0Labels permutation57 permutation7
    mixedMoment B raw18027step1 raw18027step1Labels = mixedMoment B raw18027step2 raw18027step2Labels := by
      have ha : raw18027step2 = -raw18027step1 := by apply Matrix.ext; change ∀ i j, raw18027step2 i j = -(raw18027step1 i j); unfold raw18027step2 raw18027step1; decide +kernel
      have hl : raw18027step2Labels = raw18027step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18027step2 raw18027step2Labels = mixedMoment B raw18027step3 raw18027step3Labels := by
      have ha : raw18027step3 = raw18027step2 := by apply Matrix.ext; unfold raw18027step3 raw18027step2; decide +kernel
      have hl : raw18027step2Labels = labelEmbedding1 ∘ raw18027step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18027step2 raw18027step2Labels raw18027step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3958 node3958Labels := by rfl

def raw18028 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw18028Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18028step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw18028step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18028step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![2, 0, -2], ![2, -1, -1]]
def raw18028step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18028step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, -2, 2], ![-1, 2, -1], ![-1, -1, 2]]
def raw18028step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18028step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -2, 1], ![1, 1, -2]]
def raw18028step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18028step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -2, 1], ![1, 1, -2]]
def raw18028step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18028 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18028 raw18028Labels = mixedMoment B node3631 node3631Labels := by
  calc
    mixedMoment B raw18028 raw18028Labels = mixedMoment B raw18028step0 raw18028step0Labels := by
      have hz : ∀ j, raw18028 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18028step0 = (fun i j => raw18028 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18028step0 raw18028; decide +kernel
      have hl : raw18028step0Labels = raw18028Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18028 raw18028Labels permutation434 hz
    mixedMoment B raw18028step0 raw18028step0Labels = mixedMoment B raw18028step1 raw18028step1Labels := by
      have hz : ∀ j, raw18028step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw18028step1 = (fun i j => raw18028step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw18028step1 raw18028step0; decide +kernel
      have hl : raw18028step1Labels = raw18028step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18028step0 raw18028step0Labels permutation80 hz
    mixedMoment B raw18028step1 raw18028step1Labels = mixedMoment B raw18028step2 raw18028step2Labels := by
      have ha : raw18028step2 = (fun i j => raw18028step1 (permutation10 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18028step2 raw18028step1; decide +kernel
      have hl : raw18028step2Labels = raw18028step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18028step1 raw18028step1Labels permutation10 permutation5
    mixedMoment B raw18028step2 raw18028step2Labels = mixedMoment B raw18028step3 raw18028step3Labels := by
      have ha : raw18028step3 = -raw18028step2 := by apply Matrix.ext; change ∀ i j, raw18028step3 i j = -(raw18028step2 i j); unfold raw18028step3 raw18028step2; decide +kernel
      have hl : raw18028step3Labels = raw18028step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18028step3 raw18028step3Labels = mixedMoment B raw18028step4 raw18028step4Labels := by
      have ha : raw18028step4 = raw18028step3 := by apply Matrix.ext; unfold raw18028step4 raw18028step3; decide +kernel
      have hl : raw18028step3Labels = labelEmbedding1 ∘ raw18028step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18028step3 raw18028step3Labels raw18028step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3631 node3631Labels := by rfl

def raw18029 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw18029Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18029step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw18029step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18029step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![2, 0, -2], ![2, -1, -1]]
def raw18029step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18029step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![1, 1, -2], ![2, 0, -2]]
def raw18029step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18029step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![1, 1, -2], ![2, 0, -2]]
def raw18029step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18029 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18029 raw18029Labels = mixedMoment B node3775 node3775Labels := by
  calc
    mixedMoment B raw18029 raw18029Labels = mixedMoment B raw18029step0 raw18029step0Labels := by
      have hz : ∀ j, raw18029 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18029step0 = (fun i j => raw18029 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18029step0 raw18029; decide +kernel
      have hl : raw18029step0Labels = raw18029Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18029 raw18029Labels permutation434 hz
    mixedMoment B raw18029step0 raw18029step0Labels = mixedMoment B raw18029step1 raw18029step1Labels := by
      have hz : ∀ j, raw18029step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw18029step1 = (fun i j => raw18029step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw18029step1 raw18029step0; decide +kernel
      have hl : raw18029step1Labels = raw18029step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18029step0 raw18029step0Labels permutation80 hz
    mixedMoment B raw18029step1 raw18029step1Labels = mixedMoment B raw18029step2 raw18029step2Labels := by
      have ha : raw18029step2 = (fun i j => raw18029step1 (permutation24 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18029step2 raw18029step1; decide +kernel
      have hl : raw18029step2Labels = raw18029step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18029step1 raw18029step1Labels permutation24 permutation7
    mixedMoment B raw18029step2 raw18029step2Labels = mixedMoment B raw18029step3 raw18029step3Labels := by
      have ha : raw18029step3 = raw18029step2 := by apply Matrix.ext; unfold raw18029step3 raw18029step2; decide +kernel
      have hl : raw18029step2Labels = labelEmbedding1 ∘ raw18029step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18029step2 raw18029step2Labels raw18029step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3775 node3775Labels := by rfl

def raw18030 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw18030Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18030step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw18030step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18030step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw18030step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18030step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw18030step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18030 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18030 raw18030Labels = mixedMoment B node3767 node3767Labels := by
  calc
    mixedMoment B raw18030 raw18030Labels = mixedMoment B raw18030step0 raw18030step0Labels := by
      have hz : ∀ j, raw18030 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18030step0 = (fun i j => raw18030 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18030step0 raw18030; decide +kernel
      have hl : raw18030step0Labels = raw18030Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18030 raw18030Labels permutation434 hz
    mixedMoment B raw18030step0 raw18030step0Labels = mixedMoment B raw18030step1 raw18030step1Labels := by
      have ha : raw18030step1 = (fun i j => raw18030step0 (permutation126 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18030step1 raw18030step0; decide +kernel
      have hl : raw18030step1Labels = raw18030step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18030step0 raw18030step0Labels permutation126 permutation7
    mixedMoment B raw18030step1 raw18030step1Labels = mixedMoment B raw18030step2 raw18030step2Labels := by
      have ha : raw18030step2 = raw18030step1 := by apply Matrix.ext; unfold raw18030step2 raw18030step1; decide +kernel
      have hl : raw18030step1Labels = labelEmbedding1 ∘ raw18030step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18030step1 raw18030step1Labels raw18030step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3767 node3767Labels := by rfl

def raw18031 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw18031Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18031step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw18031step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18031step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw18031step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18031step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw18031step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18031 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18031 raw18031Labels = mixedMoment B node3767 node3767Labels := by
  calc
    mixedMoment B raw18031 raw18031Labels = mixedMoment B raw18031step0 raw18031step0Labels := by
      have hz : ∀ j, raw18031 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18031step0 = (fun i j => raw18031 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18031step0 raw18031; decide +kernel
      have hl : raw18031step0Labels = raw18031Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18031 raw18031Labels permutation346 hz
    mixedMoment B raw18031step0 raw18031step0Labels = mixedMoment B raw18031step1 raw18031step1Labels := by
      have ha : raw18031step1 = (fun i j => raw18031step0 (permutation126 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18031step1 raw18031step0; decide +kernel
      have hl : raw18031step1Labels = raw18031step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18031step0 raw18031step0Labels permutation126 permutation7
    mixedMoment B raw18031step1 raw18031step1Labels = mixedMoment B raw18031step2 raw18031step2Labels := by
      have ha : raw18031step2 = raw18031step1 := by apply Matrix.ext; unfold raw18031step2 raw18031step1; decide +kernel
      have hl : raw18031step1Labels = labelEmbedding1 ∘ raw18031step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18031step1 raw18031step1Labels raw18031step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3767 node3767Labels := by rfl

def raw18032 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw18032Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18032step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw18032step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18032step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![2, 0, -2], ![1, 0, -1]]
def raw18032step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18032step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw18032step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18032step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw18032step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18032 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18032 raw18032Labels = mixedMoment B node3817 node3817Labels := by
  calc
    mixedMoment B raw18032 raw18032Labels = mixedMoment B raw18032step0 raw18032step0Labels := by
      have hz : ∀ j, raw18032 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18032step0 = (fun i j => raw18032 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18032step0 raw18032; decide +kernel
      have hl : raw18032step0Labels = raw18032Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18032 raw18032Labels permutation434 hz
    mixedMoment B raw18032step0 raw18032step0Labels = mixedMoment B raw18032step1 raw18032step1Labels := by
      have hz : ∀ j, raw18032step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw18032step1 = (fun i j => raw18032step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw18032step1 raw18032step0; decide +kernel
      have hl : raw18032step1Labels = raw18032step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18032step0 raw18032step0Labels permutation80 hz
    mixedMoment B raw18032step1 raw18032step1Labels = mixedMoment B raw18032step2 raw18032step2Labels := by
      have ha : raw18032step2 = (fun i j => raw18032step1 (permutation24 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18032step2 raw18032step1; decide +kernel
      have hl : raw18032step2Labels = raw18032step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18032step1 raw18032step1Labels permutation24 permutation7
    mixedMoment B raw18032step2 raw18032step2Labels = mixedMoment B raw18032step3 raw18032step3Labels := by
      have ha : raw18032step3 = raw18032step2 := by apply Matrix.ext; unfold raw18032step3 raw18032step2; decide +kernel
      have hl : raw18032step2Labels = labelEmbedding1 ∘ raw18032step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18032step2 raw18032step2Labels raw18032step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3817 node3817Labels := by rfl

def raw18033 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw18033Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18033step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw18033step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18033step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 1, -2], ![3, -2, -1]]
def raw18033step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18033step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -2, 1], ![2, 1, -3]]
def raw18033step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18033step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -2, 1], ![2, 1, -3]]
def raw18033step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18033 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18033 raw18033Labels = mixedMoment B node3579 node3579Labels := by
  calc
    mixedMoment B raw18033 raw18033Labels = mixedMoment B raw18033step0 raw18033step0Labels := by
      have hz : ∀ j, raw18033 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18033step0 = (fun i j => raw18033 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18033step0 raw18033; decide +kernel
      have hl : raw18033step0Labels = raw18033Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18033 raw18033Labels permutation434 hz
    mixedMoment B raw18033step0 raw18033step0Labels = mixedMoment B raw18033step1 raw18033step1Labels := by
      have hz : ∀ j, raw18033step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw18033step1 = (fun i j => raw18033step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw18033step1 raw18033step0; decide +kernel
      have hl : raw18033step1Labels = raw18033step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18033step0 raw18033step0Labels permutation80 hz
    mixedMoment B raw18033step1 raw18033step1Labels = mixedMoment B raw18033step2 raw18033step2Labels := by
      have ha : raw18033step2 = (fun i j => raw18033step1 (permutation29 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18033step2 raw18033step1; decide +kernel
      have hl : raw18033step2Labels = raw18033step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18033step1 raw18033step1Labels permutation29 permutation5
    mixedMoment B raw18033step2 raw18033step2Labels = mixedMoment B raw18033step3 raw18033step3Labels := by
      have ha : raw18033step3 = raw18033step2 := by apply Matrix.ext; unfold raw18033step3 raw18033step2; decide +kernel
      have hl : raw18033step2Labels = labelEmbedding1 ∘ raw18033step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18033step2 raw18033step2Labels raw18033step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3579 node3579Labels := by rfl

def raw18034 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw18034Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18034step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw18034step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18034step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, 1, -2], ![3, -2, -1]]
def raw18034step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18034step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -2, 1], ![1, 1, -2]]
def raw18034step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18034step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -2, 1], ![1, 1, -2]]
def raw18034step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18034 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18034 raw18034Labels = mixedMoment B node3631 node3631Labels := by
  calc
    mixedMoment B raw18034 raw18034Labels = mixedMoment B raw18034step0 raw18034step0Labels := by
      have hz : ∀ j, raw18034 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18034step0 = (fun i j => raw18034 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18034step0 raw18034; decide +kernel
      have hl : raw18034step0Labels = raw18034Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18034 raw18034Labels permutation434 hz
    mixedMoment B raw18034step0 raw18034step0Labels = mixedMoment B raw18034step1 raw18034step1Labels := by
      have hz : ∀ j, raw18034step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw18034step1 = (fun i j => raw18034step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw18034step1 raw18034step0; decide +kernel
      have hl : raw18034step1Labels = raw18034step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18034step0 raw18034step0Labels permutation80 hz
    mixedMoment B raw18034step1 raw18034step1Labels = mixedMoment B raw18034step2 raw18034step2Labels := by
      have ha : raw18034step2 = (fun i j => raw18034step1 (permutation29 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18034step2 raw18034step1; decide +kernel
      have hl : raw18034step2Labels = raw18034step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18034step1 raw18034step1Labels permutation29 permutation5
    mixedMoment B raw18034step2 raw18034step2Labels = mixedMoment B raw18034step3 raw18034step3Labels := by
      have ha : raw18034step3 = raw18034step2 := by apply Matrix.ext; unfold raw18034step3 raw18034step2; decide +kernel
      have hl : raw18034step2Labels = labelEmbedding1 ∘ raw18034step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18034step2 raw18034step2Labels raw18034step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3631 node3631Labels := by rfl

def raw18035 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw18035Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18035step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw18035step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18035step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18035step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18035step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18035step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18035 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18035 raw18035Labels = mixedMoment B node3578 node3578Labels := by
  calc
    mixedMoment B raw18035 raw18035Labels = mixedMoment B raw18035step0 raw18035step0Labels := by
      have hz : ∀ j, raw18035 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18035step0 = (fun i j => raw18035 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18035step0 raw18035; decide +kernel
      have hl : raw18035step0Labels = raw18035Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18035 raw18035Labels permutation434 hz
    mixedMoment B raw18035step0 raw18035step0Labels = mixedMoment B raw18035step1 raw18035step1Labels := by
      have ha : raw18035step1 = (fun i j => raw18035step0 (permutation139 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18035step1 raw18035step0; decide +kernel
      have hl : raw18035step1Labels = raw18035step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18035step0 raw18035step0Labels permutation139 permutation5
    mixedMoment B raw18035step1 raw18035step1Labels = mixedMoment B raw18035step2 raw18035step2Labels := by
      have ha : raw18035step2 = raw18035step1 := by apply Matrix.ext; unfold raw18035step2 raw18035step1; decide +kernel
      have hl : raw18035step1Labels = labelEmbedding1 ∘ raw18035step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18035step1 raw18035step1Labels raw18035step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3578 node3578Labels := by rfl

def raw18036 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw18036Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18036step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw18036step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18036step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18036step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18036step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18036step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18036 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18036 raw18036Labels = mixedMoment B node3578 node3578Labels := by
  calc
    mixedMoment B raw18036 raw18036Labels = mixedMoment B raw18036step0 raw18036step0Labels := by
      have hz : ∀ j, raw18036 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18036step0 = (fun i j => raw18036 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18036step0 raw18036; decide +kernel
      have hl : raw18036step0Labels = raw18036Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18036 raw18036Labels permutation346 hz
    mixedMoment B raw18036step0 raw18036step0Labels = mixedMoment B raw18036step1 raw18036step1Labels := by
      have ha : raw18036step1 = (fun i j => raw18036step0 (permutation139 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18036step1 raw18036step0; decide +kernel
      have hl : raw18036step1Labels = raw18036step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18036step0 raw18036step0Labels permutation139 permutation5
    mixedMoment B raw18036step1 raw18036step1Labels = mixedMoment B raw18036step2 raw18036step2Labels := by
      have ha : raw18036step2 = raw18036step1 := by apply Matrix.ext; unfold raw18036step2 raw18036step1; decide +kernel
      have hl : raw18036step1Labels = labelEmbedding1 ∘ raw18036step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18036step1 raw18036step1Labels raw18036step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3578 node3578Labels := by rfl

def raw18037 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![3, -2, -1]]
def raw18037Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18037step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 2, -2], ![3, -2, -1]]
def raw18037step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18037step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 2, -2], ![3, -2, -1]]
def raw18037step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18037step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18037step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18037step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18037step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18037 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18037 raw18037Labels = mixedMoment B node3584 node3584Labels := by
  calc
    mixedMoment B raw18037 raw18037Labels = mixedMoment B raw18037step0 raw18037step0Labels := by
      have hz : ∀ j, raw18037 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18037step0 = (fun i j => raw18037 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18037step0 raw18037; decide +kernel
      have hl : raw18037step0Labels = raw18037Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18037 raw18037Labels permutation434 hz
    mixedMoment B raw18037step0 raw18037step0Labels = mixedMoment B raw18037step1 raw18037step1Labels := by
      have hz : ∀ j, raw18037step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw18037step1 = (fun i j => raw18037step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw18037step1 raw18037step0; decide +kernel
      have hl : raw18037step1Labels = raw18037step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18037step0 raw18037step0Labels permutation80 hz
    mixedMoment B raw18037step1 raw18037step1Labels = mixedMoment B raw18037step2 raw18037step2Labels := by
      have ha : raw18037step2 = (fun i j => raw18037step1 (permutation28 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18037step2 raw18037step1; decide +kernel
      have hl : raw18037step2Labels = raw18037step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18037step1 raw18037step1Labels permutation28 permutation5
    mixedMoment B raw18037step2 raw18037step2Labels = mixedMoment B raw18037step3 raw18037step3Labels := by
      have ha : raw18037step3 = raw18037step2 := by apply Matrix.ext; unfold raw18037step3 raw18037step2; decide +kernel
      have hl : raw18037step2Labels = labelEmbedding1 ∘ raw18037step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18037step2 raw18037step2Labels raw18037step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3584 node3584Labels := by rfl

def raw18038 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw18038Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18038step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 3, -1], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw18038step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18038step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 3, -1], ![1, -2, 1], ![2, -1, -1]]
def raw18038step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18038step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw18038step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18038step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw18038step3Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18038step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw18038step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18038 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18038 raw18038Labels = mixedMoment B node5275 node5275Labels := by
  calc
    mixedMoment B raw18038 raw18038Labels = mixedMoment B raw18038step0 raw18038step0Labels := by
      have hz : ∀ j, raw18038 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18038step0 = (fun i j => raw18038 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18038step0 raw18038; decide +kernel
      have hl : raw18038step0Labels = raw18038Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18038 raw18038Labels permutation434 hz
    mixedMoment B raw18038step0 raw18038step0Labels = mixedMoment B raw18038step1 raw18038step1Labels := by
      have hz : ∀ j, raw18038step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw18038step1 = (fun i j => raw18038step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw18038step1 raw18038step0; decide +kernel
      have hl : raw18038step1Labels = raw18038step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18038step0 raw18038step0Labels permutation80 hz
    mixedMoment B raw18038step1 raw18038step1Labels = mixedMoment B raw18038step2 raw18038step2Labels := by
      have ha : raw18038step2 = (fun i j => raw18038step1 (permutation15 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18038step2 raw18038step1; decide +kernel
      have hl : raw18038step2Labels = raw18038step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18038step1 raw18038step1Labels permutation15 permutation5
    mixedMoment B raw18038step2 raw18038step2Labels = mixedMoment B raw18038step3 raw18038step3Labels := by
      have ha : raw18038step3 = -raw18038step2 := by apply Matrix.ext; change ∀ i j, raw18038step3 i j = -(raw18038step2 i j); unfold raw18038step3 raw18038step2; decide +kernel
      have hl : raw18038step3Labels = raw18038step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18038step3 raw18038step3Labels = mixedMoment B raw18038step4 raw18038step4Labels := by
      have ha : raw18038step4 = raw18038step3 := by apply Matrix.ext; unfold raw18038step4 raw18038step3; decide +kernel
      have hl : raw18038step3Labels = labelEmbedding8 ∘ raw18038step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18038step3 raw18038step3Labels raw18038step4Labels labelEmbedding8 hl
    _ = mixedMoment B node5275 node5275Labels := by rfl

def raw18039 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 2, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw18039Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18039step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 2, -1], ![-1, 1, 0], ![1, -2, 1], ![2, -1, -1]]
def raw18039step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18039step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18039step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18039step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18039step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18039 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18039 raw18039Labels = mixedMoment B node5473 node5473Labels := by
  calc
    mixedMoment B raw18039 raw18039Labels = mixedMoment B raw18039step0 raw18039step0Labels := by
      have hz : ∀ j, raw18039 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18039step0 = (fun i j => raw18039 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18039step0 raw18039; decide +kernel
      have hl : raw18039step0Labels = raw18039Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18039 raw18039Labels permutation434 hz
    mixedMoment B raw18039step0 raw18039step0Labels = mixedMoment B raw18039step1 raw18039step1Labels := by
      have ha : raw18039step1 = (fun i j => raw18039step0 (permutation123 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18039step1 raw18039step0; decide +kernel
      have hl : raw18039step1Labels = raw18039step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18039step0 raw18039step0Labels permutation123 permutation5
    mixedMoment B raw18039step1 raw18039step1Labels = mixedMoment B raw18039step2 raw18039step2Labels := by
      have ha : raw18039step2 = raw18039step1 := by apply Matrix.ext; unfold raw18039step2 raw18039step1; decide +kernel
      have hl : raw18039step1Labels = labelEmbedding8 ∘ raw18039step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18039step1 raw18039step1Labels raw18039step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5473 node5473Labels := by rfl

def raw18040 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 2, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![2, -1, -1]]
def raw18040Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18040step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 2, -1], ![-1, 1, 0], ![1, -2, 1], ![2, -1, -1]]
def raw18040step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18040step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18040step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18040step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18040step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18040 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18040 raw18040Labels = mixedMoment B node5473 node5473Labels := by
  calc
    mixedMoment B raw18040 raw18040Labels = mixedMoment B raw18040step0 raw18040step0Labels := by
      have hz : ∀ j, raw18040 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18040step0 = (fun i j => raw18040 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18040step0 raw18040; decide +kernel
      have hl : raw18040step0Labels = raw18040Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18040 raw18040Labels permutation346 hz
    mixedMoment B raw18040step0 raw18040step0Labels = mixedMoment B raw18040step1 raw18040step1Labels := by
      have ha : raw18040step1 = (fun i j => raw18040step0 (permutation123 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18040step1 raw18040step0; decide +kernel
      have hl : raw18040step1Labels = raw18040step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18040step0 raw18040step0Labels permutation123 permutation5
    mixedMoment B raw18040step1 raw18040step1Labels = mixedMoment B raw18040step2 raw18040step2Labels := by
      have ha : raw18040step2 = raw18040step1 := by apply Matrix.ext; unfold raw18040step2 raw18040step1; decide +kernel
      have hl : raw18040step1Labels = labelEmbedding8 ∘ raw18040step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18040step1 raw18040step1Labels raw18040step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5473 node5473Labels := by rfl

def raw18041 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1]]
def raw18041Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18041step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1]]
def raw18041step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18041step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1]]
def raw18041step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18041step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw18041step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18041step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18041step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18041step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18041step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18041 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18041 raw18041Labels = mixedMoment B node5492 node5492Labels := by
  calc
    mixedMoment B raw18041 raw18041Labels = mixedMoment B raw18041step0 raw18041step0Labels := by
      have hz : ∀ j, raw18041 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18041step0 = (fun i j => raw18041 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18041step0 raw18041; decide +kernel
      have hl : raw18041step0Labels = raw18041Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18041 raw18041Labels permutation434 hz
    mixedMoment B raw18041step0 raw18041step0Labels = mixedMoment B raw18041step1 raw18041step1Labels := by
      have hz : ∀ j, raw18041step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw18041step1 = (fun i j => raw18041step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw18041step1 raw18041step0; decide +kernel
      have hl : raw18041step1Labels = raw18041step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18041step0 raw18041step0Labels permutation80 hz
    mixedMoment B raw18041step1 raw18041step1Labels = mixedMoment B raw18041step2 raw18041step2Labels := by
      have ha : raw18041step2 = (fun i j => raw18041step1 (permutation30 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18041step2 raw18041step1; decide +kernel
      have hl : raw18041step2Labels = raw18041step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18041step1 raw18041step1Labels permutation30 permutation3
    mixedMoment B raw18041step2 raw18041step2Labels = mixedMoment B raw18041step3 raw18041step3Labels := by
      have ha : raw18041step3 = -raw18041step2 := by apply Matrix.ext; change ∀ i j, raw18041step3 i j = -(raw18041step2 i j); unfold raw18041step3 raw18041step2; decide +kernel
      have hl : raw18041step3Labels = raw18041step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18041step3 raw18041step3Labels = mixedMoment B raw18041step4 raw18041step4Labels := by
      have ha : raw18041step4 = raw18041step3 := by apply Matrix.ext; unfold raw18041step4 raw18041step3; decide +kernel
      have hl : raw18041step3Labels = labelEmbedding6 ∘ raw18041step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18041step3 raw18041step3Labels raw18041step4Labels labelEmbedding6 hl
    _ = mixedMoment B node5492 node5492Labels := by rfl

def raw18042 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1]]
def raw18042Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18042step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 2, -1], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1]]
def raw18042step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18042step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1]]
def raw18042step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18042step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw18042step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18042step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw18042step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18042 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18042 raw18042Labels = mixedMoment B node5491 node5491Labels := by
  calc
    mixedMoment B raw18042 raw18042Labels = mixedMoment B raw18042step0 raw18042step0Labels := by
      have hz : ∀ j, raw18042 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18042step0 = (fun i j => raw18042 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18042step0 raw18042; decide +kernel
      have hl : raw18042step0Labels = raw18042Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18042 raw18042Labels permutation434 hz
    mixedMoment B raw18042step0 raw18042step0Labels = mixedMoment B raw18042step1 raw18042step1Labels := by
      have hz : ∀ j, raw18042step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw18042step1 = (fun i j => raw18042step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw18042step1 raw18042step0; decide +kernel
      have hl : raw18042step1Labels = raw18042step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18042step0 raw18042step0Labels permutation80 hz
    mixedMoment B raw18042step1 raw18042step1Labels = mixedMoment B raw18042step2 raw18042step2Labels := by
      have ha : raw18042step2 = (fun i j => raw18042step1 (permutation21 i) (permutation4 j)) := by apply Matrix.ext; unfold raw18042step2 raw18042step1; decide +kernel
      have hl : raw18042step2Labels = raw18042step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18042step1 raw18042step1Labels permutation21 permutation4
    mixedMoment B raw18042step2 raw18042step2Labels = mixedMoment B raw18042step3 raw18042step3Labels := by
      have ha : raw18042step3 = raw18042step2 := by apply Matrix.ext; unfold raw18042step3 raw18042step2; decide +kernel
      have hl : raw18042step2Labels = labelEmbedding7 ∘ raw18042step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18042step2 raw18042step2Labels raw18042step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5491 node5491Labels := by rfl

def raw18043 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw18043Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18043step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw18043step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18043step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw18043step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18043step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw18043step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18043step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw18043step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18043 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18043 raw18043Labels = mixedMoment B node5275 node5275Labels := by
  calc
    mixedMoment B raw18043 raw18043Labels = mixedMoment B raw18043step0 raw18043step0Labels := by
      have hz : ∀ j, raw18043 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18043step0 = (fun i j => raw18043 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18043step0 raw18043; decide +kernel
      have hl : raw18043step0Labels = raw18043Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18043 raw18043Labels permutation434 hz
    mixedMoment B raw18043step0 raw18043step0Labels = mixedMoment B raw18043step1 raw18043step1Labels := by
      have hz : ∀ j, raw18043step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw18043step1 = (fun i j => raw18043step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw18043step1 raw18043step0; decide +kernel
      have hl : raw18043step1Labels = raw18043step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18043step0 raw18043step0Labels permutation80 hz
    mixedMoment B raw18043step1 raw18043step1Labels = mixedMoment B raw18043step2 raw18043step2Labels := by
      have ha : raw18043step2 = (fun i j => raw18043step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18043step2 raw18043step1; decide +kernel
      have hl : raw18043step2Labels = raw18043step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18043step1 raw18043step1Labels permutation8 permutation3
    mixedMoment B raw18043step2 raw18043step2Labels = mixedMoment B raw18043step3 raw18043step3Labels := by
      have ha : raw18043step3 = raw18043step2 := by apply Matrix.ext; unfold raw18043step3 raw18043step2; decide +kernel
      have hl : raw18043step2Labels = labelEmbedding6 ∘ raw18043step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18043step2 raw18043step2Labels raw18043step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5275 node5275Labels := by rfl

def raw18044 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw18044Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18044step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![-1, 1, 0], ![1, -2, 1], ![2, -1, -1]]
def raw18044step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18044step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw18044step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18044step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18044step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18044step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18044step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18044 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18044 raw18044Labels = mixedMoment B node5473 node5473Labels := by
  calc
    mixedMoment B raw18044 raw18044Labels = mixedMoment B raw18044step0 raw18044step0Labels := by
      have hz : ∀ j, raw18044 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18044step0 = (fun i j => raw18044 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18044step0 raw18044; decide +kernel
      have hl : raw18044step0Labels = raw18044Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18044 raw18044Labels permutation434 hz
    mixedMoment B raw18044step0 raw18044step0Labels = mixedMoment B raw18044step1 raw18044step1Labels := by
      have ha : raw18044step1 = (fun i j => raw18044step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18044step1 raw18044step0; decide +kernel
      have hl : raw18044step1Labels = raw18044step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18044step0 raw18044step0Labels permutation149 permutation3
    mixedMoment B raw18044step1 raw18044step1Labels = mixedMoment B raw18044step2 raw18044step2Labels := by
      have ha : raw18044step2 = -raw18044step1 := by apply Matrix.ext; change ∀ i j, raw18044step2 i j = -(raw18044step1 i j); unfold raw18044step2 raw18044step1; decide +kernel
      have hl : raw18044step2Labels = raw18044step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18044step2 raw18044step2Labels = mixedMoment B raw18044step3 raw18044step3Labels := by
      have ha : raw18044step3 = raw18044step2 := by apply Matrix.ext; unfold raw18044step3 raw18044step2; decide +kernel
      have hl : raw18044step2Labels = labelEmbedding6 ∘ raw18044step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18044step2 raw18044step2Labels raw18044step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5473 node5473Labels := by rfl

def raw18045 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![2, -1, -1]]
def raw18045Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18045step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![-1, 1, 0], ![1, -2, 1], ![2, -1, -1]]
def raw18045step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18045step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw18045step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18045step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18045step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18045step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18045step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18045 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18045 raw18045Labels = mixedMoment B node5473 node5473Labels := by
  calc
    mixedMoment B raw18045 raw18045Labels = mixedMoment B raw18045step0 raw18045step0Labels := by
      have hz : ∀ j, raw18045 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18045step0 = (fun i j => raw18045 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18045step0 raw18045; decide +kernel
      have hl : raw18045step0Labels = raw18045Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18045 raw18045Labels permutation346 hz
    mixedMoment B raw18045step0 raw18045step0Labels = mixedMoment B raw18045step1 raw18045step1Labels := by
      have ha : raw18045step1 = (fun i j => raw18045step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18045step1 raw18045step0; decide +kernel
      have hl : raw18045step1Labels = raw18045step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18045step0 raw18045step0Labels permutation149 permutation3
    mixedMoment B raw18045step1 raw18045step1Labels = mixedMoment B raw18045step2 raw18045step2Labels := by
      have ha : raw18045step2 = -raw18045step1 := by apply Matrix.ext; change ∀ i j, raw18045step2 i j = -(raw18045step1 i j); unfold raw18045step2 raw18045step1; decide +kernel
      have hl : raw18045step2Labels = raw18045step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18045step2 raw18045step2Labels = mixedMoment B raw18045step3 raw18045step3Labels := by
      have ha : raw18045step3 = raw18045step2 := by apply Matrix.ext; unfold raw18045step3 raw18045step2; decide +kernel
      have hl : raw18045step2Labels = labelEmbedding6 ∘ raw18045step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18045step2 raw18045step2Labels raw18045step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5473 node5473Labels := by rfl

def raw18046 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1]]
def raw18046Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18046step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1]]
def raw18046step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18046step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1]]
def raw18046step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18046step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw18046step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18046 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18046 raw18046Labels = mixedMoment B node5491 node5491Labels := by
  calc
    mixedMoment B raw18046 raw18046Labels = mixedMoment B raw18046step0 raw18046step0Labels := by
      have hz : ∀ j, raw18046 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18046step0 = (fun i j => raw18046 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18046step0 raw18046; decide +kernel
      have hl : raw18046step0Labels = raw18046Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18046 raw18046Labels permutation434 hz
    mixedMoment B raw18046step0 raw18046step0Labels = mixedMoment B raw18046step1 raw18046step1Labels := by
      have hz : ∀ j, raw18046step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw18046step1 = (fun i j => raw18046step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw18046step1 raw18046step0; decide +kernel
      have hl : raw18046step1Labels = raw18046step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18046step0 raw18046step0Labels permutation80 hz
    mixedMoment B raw18046step1 raw18046step1Labels = mixedMoment B raw18046step2 raw18046step2Labels := by
      have ha : raw18046step2 = (fun i j => raw18046step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18046step2 raw18046step1; decide +kernel
      have hl : raw18046step2Labels = raw18046step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18046step1 raw18046step1Labels permutation10 permutation2
    _ = mixedMoment B node5491 node5491Labels := by rfl

def raw18047 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1]]
def raw18047Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18047step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1]]
def raw18047step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18047step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw18047step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18047step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18047step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18047step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18047step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18047 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18047 raw18047Labels = mixedMoment B node5492 node5492Labels := by
  calc
    mixedMoment B raw18047 raw18047Labels = mixedMoment B raw18047step0 raw18047step0Labels := by
      have hz : ∀ j, raw18047 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18047step0 = (fun i j => raw18047 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18047step0 raw18047; decide +kernel
      have hl : raw18047step0Labels = raw18047Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18047 raw18047Labels permutation434 hz
    mixedMoment B raw18047step0 raw18047step0Labels = mixedMoment B raw18047step1 raw18047step1Labels := by
      have hz : ∀ j, raw18047step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw18047step1 = (fun i j => raw18047step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw18047step1 raw18047step0; decide +kernel
      have hl : raw18047step1Labels = raw18047step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18047step0 raw18047step0Labels permutation80 hz
    mixedMoment B raw18047step1 raw18047step1Labels = mixedMoment B raw18047step2 raw18047step2Labels := by
      have ha : raw18047step2 = (fun i j => raw18047step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18047step2 raw18047step1; decide +kernel
      have hl : raw18047step2Labels = raw18047step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18047step1 raw18047step1Labels permutation9 permutation3
    mixedMoment B raw18047step2 raw18047step2Labels = mixedMoment B raw18047step3 raw18047step3Labels := by
      have ha : raw18047step3 = raw18047step2 := by apply Matrix.ext; unfold raw18047step3 raw18047step2; decide +kernel
      have hl : raw18047step2Labels = labelEmbedding6 ∘ raw18047step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18047step2 raw18047step2Labels raw18047step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5492 node5492Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
