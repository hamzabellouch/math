import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes14
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes28
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes36
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes37
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes49
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes52
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes58
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes67
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes73
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes74

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw31872 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw31872Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31872step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![1, -1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw31872step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31872step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw31872step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw31872step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw31872step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31872 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31872 raw31872Labels = mixedMoment B node4745 node4745Labels := by
  calc
    mixedMoment B raw31872 raw31872Labels = mixedMoment B raw31872step0 raw31872step0Labels := by
      have hz : ∀ j, raw31872 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31872step0 = (fun i j => raw31872 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31872step0 raw31872; decide +kernel
      have hl : raw31872step0Labels = raw31872Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31872 raw31872Labels permutation346 hz
    mixedMoment B raw31872step0 raw31872step0Labels = mixedMoment B raw31872step1 raw31872step1Labels := by
      have ha : raw31872step1 = (fun i j => raw31872step0 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw31872step1 raw31872step0; decide +kernel
      have hl : raw31872step1Labels = raw31872step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31872step0 raw31872step0Labels permutation33 permutation6
    mixedMoment B raw31872step1 raw31872step1Labels = mixedMoment B raw31872step2 raw31872step2Labels := by
      have ha : raw31872step2 = raw31872step1 := by apply Matrix.ext; unfold raw31872step2 raw31872step1; decide +kernel
      have hl : raw31872step1Labels = labelEmbedding9 ∘ raw31872step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31872step1 raw31872step1Labels raw31872step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4745 node4745Labels := by rfl

def raw31873 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, -3, 2], ![-1, -1, 2]]
def raw31873Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31873step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![0, 1, -1], ![1, -1, 0], ![1, -3, 2], ![-1, -1, 2]]
def raw31873step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31873step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, 0, -1], ![-1, 1, 0], ![-1, -1, 2], ![-3, 1, 2]]
def raw31873step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw31873step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw31873step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw31873step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw31873step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31873 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31873 raw31873Labels = mixedMoment B node4303 node4303Labels := by
  calc
    mixedMoment B raw31873 raw31873Labels = mixedMoment B raw31873step0 raw31873step0Labels := by
      have hz : ∀ j, raw31873 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31873step0 = (fun i j => raw31873 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31873step0 raw31873; decide +kernel
      have hl : raw31873step0Labels = raw31873Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31873 raw31873Labels permutation434 hz
    mixedMoment B raw31873step0 raw31873step0Labels = mixedMoment B raw31873step1 raw31873step1Labels := by
      have ha : raw31873step1 = (fun i j => raw31873step0 (permutation33 i) (permutation4 j)) := by apply Matrix.ext; unfold raw31873step1 raw31873step0; decide +kernel
      have hl : raw31873step1Labels = raw31873step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31873step0 raw31873step0Labels permutation33 permutation4
    mixedMoment B raw31873step1 raw31873step1Labels = mixedMoment B raw31873step2 raw31873step2Labels := by
      have ha : raw31873step2 = -raw31873step1 := by apply Matrix.ext; change ∀ i j, raw31873step2 i j = -(raw31873step1 i j); unfold raw31873step2 raw31873step1; decide +kernel
      have hl : raw31873step2Labels = raw31873step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31873step2 raw31873step2Labels = mixedMoment B raw31873step3 raw31873step3Labels := by
      have ha : raw31873step3 = raw31873step2 := by apply Matrix.ext; unfold raw31873step3 raw31873step2; decide +kernel
      have hl : raw31873step2Labels = labelEmbedding7 ∘ raw31873step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31873step2 raw31873step2Labels raw31873step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4303 node4303Labels := by rfl

def raw31874 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![1, -3, 2], ![-1, -1, 2]]
def raw31874Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31874step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 2, -1], ![1, -1, 0], ![1, -3, 2], ![-1, -1, 2]]
def raw31874step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31874step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-3, 1, 2]]
def raw31874step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw31874step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw31874step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw31874step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw31874step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31874 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31874 raw31874Labels = mixedMoment B node4644 node4644Labels := by
  calc
    mixedMoment B raw31874 raw31874Labels = mixedMoment B raw31874step0 raw31874step0Labels := by
      have hz : ∀ j, raw31874 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31874step0 = (fun i j => raw31874 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31874step0 raw31874; decide +kernel
      have hl : raw31874step0Labels = raw31874Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31874 raw31874Labels permutation434 hz
    mixedMoment B raw31874step0 raw31874step0Labels = mixedMoment B raw31874step1 raw31874step1Labels := by
      have ha : raw31874step1 = (fun i j => raw31874step0 (permutation33 i) (permutation4 j)) := by apply Matrix.ext; unfold raw31874step1 raw31874step0; decide +kernel
      have hl : raw31874step1Labels = raw31874step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31874step0 raw31874step0Labels permutation33 permutation4
    mixedMoment B raw31874step1 raw31874step1Labels = mixedMoment B raw31874step2 raw31874step2Labels := by
      have ha : raw31874step2 = -raw31874step1 := by apply Matrix.ext; change ∀ i j, raw31874step2 i j = -(raw31874step1 i j); unfold raw31874step2 raw31874step1; decide +kernel
      have hl : raw31874step2Labels = raw31874step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31874step2 raw31874step2Labels = mixedMoment B raw31874step3 raw31874step3Labels := by
      have ha : raw31874step3 = raw31874step2 := by apply Matrix.ext; unfold raw31874step3 raw31874step2; decide +kernel
      have hl : raw31874step2Labels = labelEmbedding7 ∘ raw31874step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31874step2 raw31874step2Labels raw31874step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4644 node4644Labels := by rfl

def raw31875 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![1, -3, 2], ![-1, -1, 2]]
def raw31875Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31875step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-3, 1, 2]]
def raw31875step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw31875step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw31875step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw31875step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw31875step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31875 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31875 raw31875Labels = mixedMoment B node4709 node4709Labels := by
  calc
    mixedMoment B raw31875 raw31875Labels = mixedMoment B raw31875step0 raw31875step0Labels := by
      have ha : raw31875step0 = (fun i j => raw31875 (permutation159 i) (permutation4 j)) := by apply Matrix.ext; unfold raw31875step0 raw31875; decide +kernel
      have hl : raw31875step0Labels = raw31875Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31875 raw31875Labels permutation159 permutation4
    mixedMoment B raw31875step0 raw31875step0Labels = mixedMoment B raw31875step1 raw31875step1Labels := by
      have ha : raw31875step1 = -raw31875step0 := by apply Matrix.ext; change ∀ i j, raw31875step1 i j = -(raw31875step0 i j); unfold raw31875step1 raw31875step0; decide +kernel
      have hl : raw31875step1Labels = raw31875step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31875step1 raw31875step1Labels = mixedMoment B raw31875step2 raw31875step2Labels := by
      have ha : raw31875step2 = raw31875step1 := by apply Matrix.ext; unfold raw31875step2 raw31875step1; decide +kernel
      have hl : raw31875step1Labels = labelEmbedding7 ∘ raw31875step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31875step1 raw31875step1Labels raw31875step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4709 node4709Labels := by rfl

def raw31876 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![0, -2, 2]]
def raw31876Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31876step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![0, 1, -1], ![1, -1, 0], ![0, -2, 2], ![0, -2, 2]]
def raw31876step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31876step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, 0, -1], ![-1, 1, 0], ![-2, 0, 2], ![-2, 0, 2]]
def raw31876step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw31876step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw31876step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw31876step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw31876step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31876 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31876 raw31876Labels = mixedMoment B node4305 node4305Labels := by
  calc
    mixedMoment B raw31876 raw31876Labels = mixedMoment B raw31876step0 raw31876step0Labels := by
      have hz : ∀ j, raw31876 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31876step0 = (fun i j => raw31876 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31876step0 raw31876; decide +kernel
      have hl : raw31876step0Labels = raw31876Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31876 raw31876Labels permutation434 hz
    mixedMoment B raw31876step0 raw31876step0Labels = mixedMoment B raw31876step1 raw31876step1Labels := by
      have ha : raw31876step1 = (fun i j => raw31876step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw31876step1 raw31876step0; decide +kernel
      have hl : raw31876step1Labels = raw31876step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31876step0 raw31876step0Labels permutation32 permutation4
    mixedMoment B raw31876step1 raw31876step1Labels = mixedMoment B raw31876step2 raw31876step2Labels := by
      have ha : raw31876step2 = -raw31876step1 := by apply Matrix.ext; change ∀ i j, raw31876step2 i j = -(raw31876step1 i j); unfold raw31876step2 raw31876step1; decide +kernel
      have hl : raw31876step2Labels = raw31876step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31876step2 raw31876step2Labels = mixedMoment B raw31876step3 raw31876step3Labels := by
      have ha : raw31876step3 = raw31876step2 := by apply Matrix.ext; unfold raw31876step3 raw31876step2; decide +kernel
      have hl : raw31876step2Labels = labelEmbedding7 ∘ raw31876step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31876step2 raw31876step2Labels raw31876step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4305 node4305Labels := by rfl

def raw31877 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 2, 0], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![2, -2, 0]]
def raw31877Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31877step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![2, -2, 0]]
def raw31877step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31877step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![1, -1], ![2, -2], ![2, -2]]
def raw31877step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical31877 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31877 raw31877Labels = mixedMoment B node4075 node4075Labels := by
  calc
    mixedMoment B raw31877 raw31877Labels = mixedMoment B raw31877step0 raw31877step0Labels := by
      have hz : ∀ j, raw31877 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31877step0 = (fun i j => raw31877 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31877step0 raw31877; decide +kernel
      have hl : raw31877step0Labels = raw31877Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31877 raw31877Labels permutation434 hz
    mixedMoment B raw31877step0 raw31877step0Labels = mixedMoment B raw31877step1 raw31877step1Labels := by
      have hz : ∀ i, raw31877step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw31877step1 = (fun i j => raw31877step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw31877step1 raw31877step0; decide +kernel
      have hl : raw31877step1Labels = (fun j => raw31877step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw31877step0 raw31877step0Labels permutation6 hz
    _ = mixedMoment B node4075 node4075Labels := by rfl

def raw31878 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![1, -1, 0], ![-1, 1, 0], ![2, -2, 0], ![2, -2, 0]]
def raw31878Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31878step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![-1, 1], ![2, -2], ![2, -2]]
def raw31878step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw31878step1 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![-1, 1], ![1, -1], ![2, -2], ![2, -2]]
def raw31878step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical31878 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31878 raw31878Labels = mixedMoment B node4078 node4078Labels := by
  calc
    mixedMoment B raw31878 raw31878Labels = mixedMoment B raw31878step0 raw31878step0Labels := by
      have hz : ∀ i, raw31878 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw31878step0 = (fun i j => raw31878 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw31878step0 raw31878; decide +kernel
      have hl : raw31878step0Labels = (fun j => raw31878Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw31878 raw31878Labels permutation6 hz
    mixedMoment B raw31878step0 raw31878step0Labels = mixedMoment B raw31878step1 raw31878step1Labels := by
      have ha : raw31878step1 = (fun i j => raw31878step0 (permutation158 i) (permutation0 j)) := by apply Matrix.ext; unfold raw31878step1 raw31878step0; decide +kernel
      have hl : raw31878step1Labels = raw31878step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31878step0 raw31878step0Labels permutation158 permutation0
    _ = mixedMoment B node4078 node4078Labels := by rfl

def raw31879 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0]]
def raw31879Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31879step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0]]
def raw31879step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31879step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![2, -2], ![1, -1]]
def raw31879step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw31879step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw31879step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical31879 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31879 raw31879Labels = mixedMoment B node4080 node4080Labels := by
  calc
    mixedMoment B raw31879 raw31879Labels = mixedMoment B raw31879step0 raw31879step0Labels := by
      have hz : ∀ j, raw31879 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31879step0 = (fun i j => raw31879 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31879step0 raw31879; decide +kernel
      have hl : raw31879step0Labels = raw31879Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31879 raw31879Labels permutation434 hz
    mixedMoment B raw31879step0 raw31879step0Labels = mixedMoment B raw31879step1 raw31879step1Labels := by
      have hz : ∀ i, raw31879step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw31879step1 = (fun i j => raw31879step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw31879step1 raw31879step0; decide +kernel
      have hl : raw31879step1Labels = (fun j => raw31879step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw31879step0 raw31879step0Labels permutation6 hz
    mixedMoment B raw31879step1 raw31879step1Labels = mixedMoment B raw31879step2 raw31879step2Labels := by
      have ha : raw31879step2 = (fun i j => raw31879step1 (permutation33 i) (permutation0 j)) := by apply Matrix.ext; unfold raw31879step2 raw31879step1; decide +kernel
      have hl : raw31879step2Labels = raw31879step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31879step1 raw31879step1Labels permutation33 permutation0
    _ = mixedMoment B node4080 node4080Labels := by rfl

def raw31880 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, -2, 0]]
def raw31880Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31880step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![2, -2, 0]]
def raw31880step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31880step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![1, -1], ![2, -2], ![2, -2]]
def raw31880step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical31880 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31880 raw31880Labels = mixedMoment B node4075 node4075Labels := by
  calc
    mixedMoment B raw31880 raw31880Labels = mixedMoment B raw31880step0 raw31880step0Labels := by
      have hz : ∀ j, raw31880 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31880step0 = (fun i j => raw31880 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31880step0 raw31880; decide +kernel
      have hl : raw31880step0Labels = raw31880Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31880 raw31880Labels permutation346 hz
    mixedMoment B raw31880step0 raw31880step0Labels = mixedMoment B raw31880step1 raw31880step1Labels := by
      have hz : ∀ i, raw31880step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw31880step1 = (fun i j => raw31880step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw31880step1 raw31880step0; decide +kernel
      have hl : raw31880step1Labels = (fun j => raw31880step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw31880step0 raw31880step0Labels permutation6 hz
    _ = mixedMoment B node4075 node4075Labels := by rfl

def raw31881 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, -2, 0]]
def raw31881Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31881step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![-1, 1], ![1, -1], ![2, -2], ![2, -2]]
def raw31881step0Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical31881 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31881 raw31881Labels = mixedMoment B node4078 node4078Labels := by
  calc
    mixedMoment B raw31881 raw31881Labels = mixedMoment B raw31881step0 raw31881step0Labels := by
      have hz : ∀ i, raw31881 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw31881step0 = (fun i j => raw31881 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw31881step0 raw31881; decide +kernel
      have hl : raw31881step0Labels = (fun j => raw31881Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw31881 raw31881Labels permutation6 hz
    _ = mixedMoment B node4078 node4078Labels := by rfl

def raw31882 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![2, -2, 0]]
def raw31882Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31882step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 2, 0], ![0, 0, 0], ![3, -3, 0], ![2, -2, 0]]
def raw31882step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31882step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 2, 0], ![3, -3, 0], ![2, -2, 0]]
def raw31882step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31882step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![3, -3], ![2, -2]]
def raw31882step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw31882step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![2, -2], ![3, -3]]
def raw31882step3Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical31882 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31882 raw31882Labels = mixedMoment B node4076 node4076Labels := by
  calc
    mixedMoment B raw31882 raw31882Labels = mixedMoment B raw31882step0 raw31882step0Labels := by
      have hz : ∀ j, raw31882 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31882step0 = (fun i j => raw31882 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31882step0 raw31882; decide +kernel
      have hl : raw31882step0Labels = raw31882Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31882 raw31882Labels permutation434 hz
    mixedMoment B raw31882step0 raw31882step0Labels = mixedMoment B raw31882step1 raw31882step1Labels := by
      have hz : ∀ j, raw31882step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31882step1 = (fun i j => raw31882step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31882step1 raw31882step0; decide +kernel
      have hl : raw31882step1Labels = raw31882step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31882step0 raw31882step0Labels permutation80 hz
    mixedMoment B raw31882step1 raw31882step1Labels = mixedMoment B raw31882step2 raw31882step2Labels := by
      have hz : ∀ i, raw31882step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw31882step2 = (fun i j => raw31882step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw31882step2 raw31882step1; decide +kernel
      have hl : raw31882step2Labels = (fun j => raw31882step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw31882step1 raw31882step1Labels permutation6 hz
    mixedMoment B raw31882step2 raw31882step2Labels = mixedMoment B raw31882step3 raw31882step3Labels := by
      have ha : raw31882step3 = (fun i j => raw31882step2 (permutation9 i) (permutation0 j)) := by apply Matrix.ext; unfold raw31882step3 raw31882step2; decide +kernel
      have hl : raw31882step3Labels = raw31882step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31882step2 raw31882step2Labels permutation9 permutation0
    _ = mixedMoment B node4076 node4076Labels := by rfl

def raw31883 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![3, -3, 0], ![2, -2, 0]]
def raw31883Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31883step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![-1, 1, 0], ![3, -3, 0], ![2, -2, 0]]
def raw31883step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31883step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![-1, 1], ![3, -3], ![2, -2]]
def raw31883step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw31883step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![3, -3], ![2, -2], ![-1, 1], ![-1, 1], ![-3, 3]]
def raw31883step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw31883step3 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![1, -1], ![1, -1], ![3, -3]]
def raw31883step3Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical31883 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31883 raw31883Labels = mixedMoment B node4074 node4074Labels := by
  calc
    mixedMoment B raw31883 raw31883Labels = mixedMoment B raw31883step0 raw31883step0Labels := by
      have hz : ∀ j, raw31883 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31883step0 = (fun i j => raw31883 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31883step0 raw31883; decide +kernel
      have hl : raw31883step0Labels = raw31883Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31883 raw31883Labels permutation434 hz
    mixedMoment B raw31883step0 raw31883step0Labels = mixedMoment B raw31883step1 raw31883step1Labels := by
      have hz : ∀ i, raw31883step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw31883step1 = (fun i j => raw31883step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw31883step1 raw31883step0; decide +kernel
      have hl : raw31883step1Labels = (fun j => raw31883step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw31883step0 raw31883step0Labels permutation6 hz
    mixedMoment B raw31883step1 raw31883step1Labels = mixedMoment B raw31883step2 raw31883step2Labels := by
      have ha : raw31883step2 = (fun i j => raw31883step1 (permutation125 i) (permutation0 j)) := by apply Matrix.ext; unfold raw31883step2 raw31883step1; decide +kernel
      have hl : raw31883step2Labels = raw31883step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31883step1 raw31883step1Labels permutation125 permutation0
    mixedMoment B raw31883step2 raw31883step2Labels = mixedMoment B raw31883step3 raw31883step3Labels := by
      have ha : raw31883step3 = -raw31883step2 := by apply Matrix.ext; change ∀ i j, raw31883step3 i j = -(raw31883step2 i j); unfold raw31883step3 raw31883step2; decide +kernel
      have hl : raw31883step3Labels = raw31883step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4074 node4074Labels := by rfl

def raw31884 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![3, -3, 0], ![2, -2, 0]]
def raw31884Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31884step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![-1, 1, 0], ![3, -3, 0], ![2, -2, 0]]
def raw31884step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31884step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![-1, 1], ![3, -3], ![2, -2]]
def raw31884step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw31884step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![3, -3], ![2, -2], ![-1, 1], ![-1, 1], ![-3, 3]]
def raw31884step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw31884step3 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![1, -1], ![1, -1], ![3, -3]]
def raw31884step3Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical31884 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31884 raw31884Labels = mixedMoment B node4074 node4074Labels := by
  calc
    mixedMoment B raw31884 raw31884Labels = mixedMoment B raw31884step0 raw31884step0Labels := by
      have hz : ∀ j, raw31884 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31884step0 = (fun i j => raw31884 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31884step0 raw31884; decide +kernel
      have hl : raw31884step0Labels = raw31884Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31884 raw31884Labels permutation346 hz
    mixedMoment B raw31884step0 raw31884step0Labels = mixedMoment B raw31884step1 raw31884step1Labels := by
      have hz : ∀ i, raw31884step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw31884step1 = (fun i j => raw31884step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw31884step1 raw31884step0; decide +kernel
      have hl : raw31884step1Labels = (fun j => raw31884step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw31884step0 raw31884step0Labels permutation6 hz
    mixedMoment B raw31884step1 raw31884step1Labels = mixedMoment B raw31884step2 raw31884step2Labels := by
      have ha : raw31884step2 = (fun i j => raw31884step1 (permutation125 i) (permutation0 j)) := by apply Matrix.ext; unfold raw31884step2 raw31884step1; decide +kernel
      have hl : raw31884step2Labels = raw31884step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31884step1 raw31884step1Labels permutation125 permutation0
    mixedMoment B raw31884step2 raw31884step2Labels = mixedMoment B raw31884step3 raw31884step3Labels := by
      have ha : raw31884step3 = -raw31884step2 := by apply Matrix.ext; change ∀ i j, raw31884step3 i j = -(raw31884step2 i j); unfold raw31884step3 raw31884step2; decide +kernel
      have hl : raw31884step3Labels = raw31884step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4074 node4074Labels := by rfl

def raw31885 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![1, -1, 0]]
def raw31885Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31885step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![0, 0, 0], ![3, -3, 0], ![1, -1, 0]]
def raw31885step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31885step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![3, -3, 0], ![1, -1, 0]]
def raw31885step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31885step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![3, -3], ![1, -1]]
def raw31885step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw31885step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![3, -3]]
def raw31885step3Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical31885 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31885 raw31885Labels = mixedMoment B node4081 node4081Labels := by
  calc
    mixedMoment B raw31885 raw31885Labels = mixedMoment B raw31885step0 raw31885step0Labels := by
      have hz : ∀ j, raw31885 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31885step0 = (fun i j => raw31885 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31885step0 raw31885; decide +kernel
      have hl : raw31885step0Labels = raw31885Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31885 raw31885Labels permutation434 hz
    mixedMoment B raw31885step0 raw31885step0Labels = mixedMoment B raw31885step1 raw31885step1Labels := by
      have hz : ∀ j, raw31885step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31885step1 = (fun i j => raw31885step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31885step1 raw31885step0; decide +kernel
      have hl : raw31885step1Labels = raw31885step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31885step0 raw31885step0Labels permutation80 hz
    mixedMoment B raw31885step1 raw31885step1Labels = mixedMoment B raw31885step2 raw31885step2Labels := by
      have hz : ∀ i, raw31885step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw31885step2 = (fun i j => raw31885step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw31885step2 raw31885step1; decide +kernel
      have hl : raw31885step2Labels = (fun j => raw31885step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw31885step1 raw31885step1Labels permutation6 hz
    mixedMoment B raw31885step2 raw31885step2Labels = mixedMoment B raw31885step3 raw31885step3Labels := by
      have ha : raw31885step3 = (fun i j => raw31885step2 (permutation9 i) (permutation0 j)) := by apply Matrix.ext; unfold raw31885step3 raw31885step2; decide +kernel
      have hl : raw31885step3Labels = raw31885step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31885step2 raw31885step2Labels permutation9 permutation0
    _ = mixedMoment B node4081 node4081Labels := by rfl

def raw31886 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw31886Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31886step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw31886step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31886 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31886 raw31886Labels = mixedMoment B node1806 node1806Labels := by
  calc
    mixedMoment B raw31886 raw31886Labels = mixedMoment B raw31886step0 raw31886step0Labels := by
      have ha : raw31886step0 = (fun i j => raw31886 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31886step0 raw31886; decide +kernel
      have hl : raw31886step0Labels = raw31886Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31886 raw31886Labels permutation158 permutation2
    _ = mixedMoment B node1806 node1806Labels := by rfl

def raw31887 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![0, 2, -2], ![2, -2, 0]]
def raw31887Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31887step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw31887step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31887 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31887 raw31887Labels = mixedMoment B node2034 node2034Labels := by
  calc
    mixedMoment B raw31887 raw31887Labels = mixedMoment B raw31887step0 raw31887step0Labels := by
      have ha : raw31887step0 = (fun i j => raw31887 (permutation166 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31887step0 raw31887; decide +kernel
      have hl : raw31887step0Labels = raw31887Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31887 raw31887Labels permutation166 permutation2
    _ = mixedMoment B node2034 node2034Labels := by rfl

def raw31888 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0]]
def raw31888Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31888step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw31888step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31888 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31888 raw31888Labels = mixedMoment B node2051 node2051Labels := by
  calc
    mixedMoment B raw31888 raw31888Labels = mixedMoment B raw31888step0 raw31888step0Labels := by
      have ha : raw31888step0 = (fun i j => raw31888 (permutation162 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31888step0 raw31888; decide +kernel
      have hl : raw31888step0Labels = raw31888Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31888 raw31888Labels permutation162 permutation2
    _ = mixedMoment B node2051 node2051Labels := by rfl

def raw31889 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw31889Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31889step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw31889step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31889step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw31889step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31889 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31889 raw31889Labels = mixedMoment B node3789 node3789Labels := by
  calc
    mixedMoment B raw31889 raw31889Labels = mixedMoment B raw31889step0 raw31889step0Labels := by
      have ha : raw31889step0 = (fun i j => raw31889 (permutation662 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31889step0 raw31889; decide +kernel
      have hl : raw31889step0Labels = raw31889Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31889 raw31889Labels permutation662 permutation2
    mixedMoment B raw31889step0 raw31889step0Labels = mixedMoment B raw31889step1 raw31889step1Labels := by
      have ha : raw31889step1 = -raw31889step0 := by apply Matrix.ext; change ∀ i j, raw31889step1 i j = -(raw31889step0 i j); unfold raw31889step1 raw31889step0; decide +kernel
      have hl : raw31889step1Labels = raw31889step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3789 node3789Labels := by rfl

def raw31890 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw31890Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31890step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw31890step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31890 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31890 raw31890Labels = mixedMoment B node3202 node3202Labels := by
  calc
    mixedMoment B raw31890 raw31890Labels = mixedMoment B raw31890step0 raw31890step0Labels := by
      have ha : raw31890step0 = (fun i j => raw31890 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31890step0 raw31890; decide +kernel
      have hl : raw31890step0Labels = raw31890Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31890 raw31890Labels permutation178 permutation2
    _ = mixedMoment B node3202 node3202Labels := by rfl

def raw31891 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw31891Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31891step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw31891step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31891 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31891 raw31891Labels = mixedMoment B node3202 node3202Labels := by
  calc
    mixedMoment B raw31891 raw31891Labels = mixedMoment B raw31891step0 raw31891step0Labels := by
      have ha : raw31891step0 = (fun i j => raw31891 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31891step0 raw31891; decide +kernel
      have hl : raw31891step0Labels = raw31891Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31891 raw31891Labels permutation154 permutation2
    _ = mixedMoment B node3202 node3202Labels := by rfl

def raw31892 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, 0, 1], ![2, -1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw31892Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31892step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1], ![2, -1, -1], ![2, 0, -2]]
def raw31892step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31892 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31892 raw31892Labels = mixedMoment B node3189 node3189Labels := by
  calc
    mixedMoment B raw31892 raw31892Labels = mixedMoment B raw31892step0 raw31892step0Labels := by
      have ha : raw31892step0 = (fun i j => raw31892 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31892step0 raw31892; decide +kernel
      have hl : raw31892step0Labels = raw31892Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31892 raw31892Labels permutation154 permutation2
    _ = mixedMoment B node3189 node3189Labels := by rfl

def raw31893 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw31893Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31893step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw31893step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31893 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31893 raw31893Labels = mixedMoment B node3062 node3062Labels := by
  calc
    mixedMoment B raw31893 raw31893Labels = mixedMoment B raw31893step0 raw31893step0Labels := by
      have ha : raw31893step0 = (fun i j => raw31893 (permutation533 i) (permutation4 j)) := by apply Matrix.ext; unfold raw31893step0 raw31893; decide +kernel
      have hl : raw31893step0Labels = raw31893Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31893 raw31893Labels permutation533 permutation4
    _ = mixedMoment B node3062 node3062Labels := by rfl

def raw31894 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -2, 1], ![3, -1, -2]]
def raw31894Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31894step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 3, 0]]
def raw31894step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31894step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw31894step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31894 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31894 raw31894Labels = mixedMoment B node2440 node2440Labels := by
  calc
    mixedMoment B raw31894 raw31894Labels = mixedMoment B raw31894step0 raw31894step0Labels := by
      have ha : raw31894step0 = (fun i j => raw31894 (permutation662 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31894step0 raw31894; decide +kernel
      have hl : raw31894step0Labels = raw31894Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31894 raw31894Labels permutation662 permutation2
    mixedMoment B raw31894step0 raw31894step0Labels = mixedMoment B raw31894step1 raw31894step1Labels := by
      have ha : raw31894step1 = -raw31894step0 := by apply Matrix.ext; change ∀ i j, raw31894step1 i j = -(raw31894step0 i j); unfold raw31894step1 raw31894step0; decide +kernel
      have hl : raw31894step1Labels = raw31894step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2440 node2440Labels := by rfl

def raw31895 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![-1, 1], ![1, -1], ![-1, 1], ![2, -2]]
def raw31895Labels : Fin 2 → Fin 2 := ![0, 1]

def raw31895step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![-1, 1], ![2, -2]]
def raw31895step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw31895step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![2, -2], ![1, -1], ![-1, 1], ![-1, 1], ![-1, 1]]
def raw31895step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw31895step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw31895step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical31895 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31895 raw31895Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw31895 raw31895Labels = mixedMoment B raw31895step0 raw31895step0Labels := by
      have hz : ∀ j, raw31895 (permutation152 0) j = 0 := by decide +kernel
      have ha : raw31895step0 = (fun i j => raw31895 (permutation152 i.succ) j) := by apply Matrix.ext; unfold raw31895step0 raw31895; decide +kernel
      have hl : raw31895step0Labels = raw31895Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31895 raw31895Labels permutation152 hz
    mixedMoment B raw31895step0 raw31895step0Labels = mixedMoment B raw31895step1 raw31895step1Labels := by
      have ha : raw31895step1 = (fun i j => raw31895step0 (permutation140 i) (permutation0 j)) := by apply Matrix.ext; unfold raw31895step1 raw31895step0; decide +kernel
      have hl : raw31895step1Labels = raw31895step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31895step0 raw31895step0Labels permutation140 permutation0
    mixedMoment B raw31895step1 raw31895step1Labels = mixedMoment B raw31895step2 raw31895step2Labels := by
      have ha : raw31895step2 = -raw31895step1 := by apply Matrix.ext; change ∀ i j, raw31895step2 i j = -(raw31895step1 i j); unfold raw31895step2 raw31895step1; decide +kernel
      have hl : raw31895step2Labels = raw31895step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4091 node4091Labels := by rfl

def raw31896 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw31896Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31896step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw31896step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31896step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw31896step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31896 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31896 raw31896Labels = mixedMoment B node2195 node2195Labels := by
  calc
    mixedMoment B raw31896 raw31896Labels = mixedMoment B raw31896step0 raw31896step0Labels := by
      have ha : raw31896step0 = (fun i j => raw31896 (permutation162 i) (permutation4 j)) := by apply Matrix.ext; unfold raw31896step0 raw31896; decide +kernel
      have hl : raw31896step0Labels = raw31896Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31896 raw31896Labels permutation162 permutation4
    mixedMoment B raw31896step0 raw31896step0Labels = mixedMoment B raw31896step1 raw31896step1Labels := by
      have ha : raw31896step1 = -raw31896step0 := by apply Matrix.ext; change ∀ i j, raw31896step1 i j = -(raw31896step0 i j); unfold raw31896step1 raw31896step0; decide +kernel
      have hl : raw31896step1Labels = raw31896step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2195 node2195Labels := by rfl

def raw31897 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![-1, 0, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw31897Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31897step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw31897step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31897step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw31897step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31897 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31897 raw31897Labels = mixedMoment B node3463 node3463Labels := by
  calc
    mixedMoment B raw31897 raw31897Labels = mixedMoment B raw31897step0 raw31897step0Labels := by
      have ha : raw31897step0 = (fun i j => raw31897 (permutation162 i) (permutation4 j)) := by apply Matrix.ext; unfold raw31897step0 raw31897; decide +kernel
      have hl : raw31897step0Labels = raw31897Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31897 raw31897Labels permutation162 permutation4
    mixedMoment B raw31897step0 raw31897step0Labels = mixedMoment B raw31897step1 raw31897step1Labels := by
      have ha : raw31897step1 = -raw31897step0 := by apply Matrix.ext; change ∀ i j, raw31897step1 i j = -(raw31897step0 i j); unfold raw31897step1 raw31897step0; decide +kernel
      have hl : raw31897step1Labels = raw31897step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3463 node3463Labels := by rfl

def raw31898 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw31898Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31898step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 0, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw31898step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31898step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-2, 1, 1]]
def raw31898step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31898step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]
def raw31898step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31898 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31898 raw31898Labels = mixedMoment B node3606 node3606Labels := by
  calc
    mixedMoment B raw31898 raw31898Labels = mixedMoment B raw31898step0 raw31898step0Labels := by
      have hz : ∀ j, raw31898 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31898step0 = (fun i j => raw31898 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31898step0 raw31898; decide +kernel
      have hl : raw31898step0Labels = raw31898Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31898 raw31898Labels permutation346 hz
    mixedMoment B raw31898step0 raw31898step0Labels = mixedMoment B raw31898step1 raw31898step1Labels := by
      have ha : raw31898step1 = (fun i j => raw31898step0 (permutation33 i) (permutation4 j)) := by apply Matrix.ext; unfold raw31898step1 raw31898step0; decide +kernel
      have hl : raw31898step1Labels = raw31898step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31898step0 raw31898step0Labels permutation33 permutation4
    mixedMoment B raw31898step1 raw31898step1Labels = mixedMoment B raw31898step2 raw31898step2Labels := by
      have ha : raw31898step2 = -raw31898step1 := by apply Matrix.ext; change ∀ i j, raw31898step2 i j = -(raw31898step1 i j); unfold raw31898step2 raw31898step1; decide +kernel
      have hl : raw31898step2Labels = raw31898step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3606 node3606Labels := by rfl

def raw31899 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![-2, 1, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw31899Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31899step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw31899step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31899step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw31899step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31899 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31899 raw31899Labels = mixedMoment B node3560 node3560Labels := by
  calc
    mixedMoment B raw31899 raw31899Labels = mixedMoment B raw31899step0 raw31899step0Labels := by
      have ha : raw31899step0 = (fun i j => raw31899 (permutation204 i) (permutation4 j)) := by apply Matrix.ext; unfold raw31899step0 raw31899; decide +kernel
      have hl : raw31899step0Labels = raw31899Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31899 raw31899Labels permutation204 permutation4
    mixedMoment B raw31899step0 raw31899step0Labels = mixedMoment B raw31899step1 raw31899step1Labels := by
      have ha : raw31899step1 = -raw31899step0 := by apply Matrix.ext; change ∀ i j, raw31899step1 i j = -(raw31899step0 i j); unfold raw31899step1 raw31899step0; decide +kernel
      have hl : raw31899step1Labels = raw31899step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3560 node3560Labels := by rfl

def raw31900 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw31900Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31900step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1]]
def raw31900step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31900step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw31900step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31900 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31900 raw31900Labels = mixedMoment B node3605 node3605Labels := by
  calc
    mixedMoment B raw31900 raw31900Labels = mixedMoment B raw31900step0 raw31900step0Labels := by
      have ha : raw31900step0 = (fun i j => raw31900 (permutation162 i) (permutation4 j)) := by apply Matrix.ext; unfold raw31900step0 raw31900; decide +kernel
      have hl : raw31900step0Labels = raw31900Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31900 raw31900Labels permutation162 permutation4
    mixedMoment B raw31900step0 raw31900step0Labels = mixedMoment B raw31900step1 raw31900step1Labels := by
      have ha : raw31900step1 = -raw31900step0 := by apply Matrix.ext; change ∀ i j, raw31900step1 i j = -(raw31900step0 i j); unfold raw31900step1 raw31900step0; decide +kernel
      have hl : raw31900step1Labels = raw31900step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3605 node3605Labels := by rfl

def raw31901 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![1, -2, 1], ![-3, 1, 2]]
def raw31901Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31901step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw31901step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31901 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31901 raw31901Labels = mixedMoment B node2500 node2500Labels := by
  calc
    mixedMoment B raw31901 raw31901Labels = mixedMoment B raw31901step0 raw31901step0Labels := by
      have ha : raw31901step0 = (fun i j => raw31901 (permutation664 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31901step0 raw31901; decide +kernel
      have hl : raw31901step0Labels = raw31901Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31901 raw31901Labels permutation664 permutation2
    _ = mixedMoment B node2500 node2500Labels := by rfl

def raw31902 : Matrix (Fin 6) (Fin 2) ℤ := ![![3, -3], ![1, -1], ![0, 0], ![-1, 1], ![-1, 1], ![-2, 2]]
def raw31902Labels : Fin 2 → Fin 2 := ![0, 1]

def raw31902step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![3, -3], ![1, -1], ![-1, 1], ![-1, 1], ![-2, 2]]
def raw31902step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw31902step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw31902step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical31902 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31902 raw31902Labels = mixedMoment B node4080 node4080Labels := by
  calc
    mixedMoment B raw31902 raw31902Labels = mixedMoment B raw31902step0 raw31902step0Labels := by
      have hz : ∀ j, raw31902 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31902step0 = (fun i j => raw31902 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31902step0 raw31902; decide +kernel
      have hl : raw31902step0Labels = raw31902Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31902 raw31902Labels permutation346 hz
    mixedMoment B raw31902step0 raw31902step0Labels = mixedMoment B raw31902step1 raw31902step1Labels := by
      have ha : raw31902step1 = -raw31902step0 := by apply Matrix.ext; change ∀ i j, raw31902step1 i j = -(raw31902step0 i j); unfold raw31902step1 raw31902step0; decide +kernel
      have hl : raw31902step1Labels = raw31902step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4080 node4080Labels := by rfl

def raw31903 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw31903Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31903step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw31903step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31903 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31903 raw31903Labels = mixedMoment B node1803 node1803Labels := by
  calc
    mixedMoment B raw31903 raw31903Labels = mixedMoment B raw31903step0 raw31903step0Labels := by
      have ha : raw31903step0 = (fun i j => raw31903 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31903step0 raw31903; decide +kernel
      have hl : raw31903step0Labels = raw31903Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31903 raw31903Labels permutation160 permutation2
    _ = mixedMoment B node1803 node1803Labels := by rfl

def raw31904 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw31904Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31904 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31904 raw31904Labels = mixedMoment B node2033 node2033Labels := by
  calc
    _ = mixedMoment B node2033 node2033Labels := by rfl

def raw31905 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw31905Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31905step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw31905step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31905step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw31905step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31905 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31905 raw31905Labels = mixedMoment B node2054 node2054Labels := by
  calc
    mixedMoment B raw31905 raw31905Labels = mixedMoment B raw31905step0 raw31905step0Labels := by
      have hz : ∀ j, raw31905 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31905step0 = (fun i j => raw31905 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31905step0 raw31905; decide +kernel
      have hl : raw31905step0Labels = raw31905Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31905 raw31905Labels permutation434 hz
    mixedMoment B raw31905step0 raw31905step0Labels = mixedMoment B raw31905step1 raw31905step1Labels := by
      have ha : raw31905step1 = (fun i j => raw31905step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31905step1 raw31905step0; decide +kernel
      have hl : raw31905step1Labels = raw31905step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31905step0 raw31905step0Labels permutation34 permutation2
    _ = mixedMoment B node2054 node2054Labels := by rfl

def raw31906 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1]]
def raw31906Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31906step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw31906step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31906step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw31906step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31906 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31906 raw31906Labels = mixedMoment B node2054 node2054Labels := by
  calc
    mixedMoment B raw31906 raw31906Labels = mixedMoment B raw31906step0 raw31906step0Labels := by
      have hz : ∀ j, raw31906 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw31906step0 = (fun i j => raw31906 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw31906step0 raw31906; decide +kernel
      have hl : raw31906step0Labels = raw31906Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31906 raw31906Labels permutation520 hz
    mixedMoment B raw31906step0 raw31906step0Labels = mixedMoment B raw31906step1 raw31906step1Labels := by
      have ha : raw31906step1 = (fun i j => raw31906step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31906step1 raw31906step0; decide +kernel
      have hl : raw31906step1Labels = raw31906step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31906step0 raw31906step0Labels permutation34 permutation2
    _ = mixedMoment B node2054 node2054Labels := by rfl

def raw31907 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw31907Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31907step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw31907step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31907 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31907 raw31907Labels = mixedMoment B node2051 node2051Labels := by
  calc
    mixedMoment B raw31907 raw31907Labels = mixedMoment B raw31907step0 raw31907step0Labels := by
      have ha : raw31907step0 = (fun i j => raw31907 (permutation161 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31907step0 raw31907; decide +kernel
      have hl : raw31907step0Labels = raw31907Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31907 raw31907Labels permutation161 permutation2
    _ = mixedMoment B node2051 node2051Labels := by rfl

def raw31908 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw31908Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31908step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![1, 0, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw31908step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31908step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw31908step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31908 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31908 raw31908Labels = mixedMoment B node3964 node3964Labels := by
  calc
    mixedMoment B raw31908 raw31908Labels = mixedMoment B raw31908step0 raw31908step0Labels := by
      have ha : raw31908step0 = (fun i j => raw31908 (permutation662 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31908step0 raw31908; decide +kernel
      have hl : raw31908step0Labels = raw31908Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31908 raw31908Labels permutation662 permutation2
    mixedMoment B raw31908step0 raw31908step0Labels = mixedMoment B raw31908step1 raw31908step1Labels := by
      have ha : raw31908step1 = -raw31908step0 := by apply Matrix.ext; change ∀ i j, raw31908step1 i j = -(raw31908step0 i j); unfold raw31908step1 raw31908step0; decide +kernel
      have hl : raw31908step1Labels = raw31908step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3964 node3964Labels := by rfl

def raw31909 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw31909Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31909step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw31909step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31909 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31909 raw31909Labels = mixedMoment B node3172 node3172Labels := by
  calc
    mixedMoment B raw31909 raw31909Labels = mixedMoment B raw31909step0 raw31909step0Labels := by
      have ha : raw31909step0 = (fun i j => raw31909 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31909step0 raw31909; decide +kernel
      have hl : raw31909step0Labels = raw31909Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31909 raw31909Labels permutation176 permutation2
    _ = mixedMoment B node3172 node3172Labels := by rfl

def raw31910 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw31910Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31910 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31910 raw31910Labels = mixedMoment B node3197 node3197Labels := by
  calc
    _ = mixedMoment B node3197 node3197Labels := by rfl

def raw31911 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, -1, 2], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw31911Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31911step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31911step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31911 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31911 raw31911Labels = mixedMoment B node3164 node3164Labels := by
  calc
    mixedMoment B raw31911 raw31911Labels = mixedMoment B raw31911step0 raw31911step0Labels := by
      have ha : raw31911step0 = (fun i j => raw31911 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31911step0 raw31911; decide +kernel
      have hl : raw31911step0Labels = raw31911Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31911 raw31911Labels permutation178 permutation2
    _ = mixedMoment B node3164 node3164Labels := by rfl

def raw31912 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31912Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31912step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31912step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31912 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31912 raw31912Labels = mixedMoment B node3164 node3164Labels := by
  calc
    mixedMoment B raw31912 raw31912Labels = mixedMoment B raw31912step0 raw31912step0Labels := by
      have ha : raw31912step0 = (fun i j => raw31912 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31912step0 raw31912; decide +kernel
      have hl : raw31912step0Labels = raw31912Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31912 raw31912Labels permutation176 permutation2
    _ = mixedMoment B node3164 node3164Labels := by rfl

def raw31913 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw31913Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31913step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![1, 0, -1], ![1, 0, -1], ![-1, 0, 1], ![-1, -1, 2], ![-3, 3, 0]]
def raw31913step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31913step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw31913step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31913 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31913 raw31913Labels = mixedMoment B node2895 node2895Labels := by
  calc
    mixedMoment B raw31913 raw31913Labels = mixedMoment B raw31913step0 raw31913step0Labels := by
      have ha : raw31913step0 = (fun i j => raw31913 (permutation662 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31913step0 raw31913; decide +kernel
      have hl : raw31913step0Labels = raw31913Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31913 raw31913Labels permutation662 permutation2
    mixedMoment B raw31913step0 raw31913step0Labels = mixedMoment B raw31913step1 raw31913step1Labels := by
      have ha : raw31913step1 = -raw31913step0 := by apply Matrix.ext; change ∀ i j, raw31913step1 i j = -(raw31913step0 i j); unfold raw31913step1 raw31913step0; decide +kernel
      have hl : raw31913step1Labels = raw31913step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2895 node2895Labels := by rfl

def raw31914 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![-2, 2], ![1, -1], ![1, -1], ![1, -1]]
def raw31914Labels : Fin 2 → Fin 2 := ![0, 1]

def raw31914step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![1, -1], ![1, -1], ![1, -1]]
def raw31914step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw31914step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw31914step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical31914 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31914 raw31914Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw31914 raw31914Labels = mixedMoment B raw31914step0 raw31914step0Labels := by
      have hz : ∀ j, raw31914 (permutation152 0) j = 0 := by decide +kernel
      have ha : raw31914step0 = (fun i j => raw31914 (permutation152 i.succ) j) := by apply Matrix.ext; unfold raw31914step0 raw31914; decide +kernel
      have hl : raw31914step0Labels = raw31914Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31914 raw31914Labels permutation152 hz
    mixedMoment B raw31914step0 raw31914step0Labels = mixedMoment B raw31914step1 raw31914step1Labels := by
      have ha : raw31914step1 = (fun i j => raw31914step0 (permutation56 i) (permutation0 j)) := by apply Matrix.ext; unfold raw31914step1 raw31914step0; decide +kernel
      have hl : raw31914step1Labels = raw31914step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31914step0 raw31914step0Labels permutation56 permutation0
    _ = mixedMoment B node4091 node4091Labels := by rfl

def raw31915 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw31915Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31915step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw31915step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31915step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw31915step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31915 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31915 raw31915Labels = mixedMoment B node2192 node2192Labels := by
  calc
    mixedMoment B raw31915 raw31915Labels = mixedMoment B raw31915step0 raw31915step0Labels := by
      have ha : raw31915step0 = (fun i j => raw31915 (permutation161 i) (permutation4 j)) := by apply Matrix.ext; unfold raw31915step0 raw31915; decide +kernel
      have hl : raw31915step0Labels = raw31915Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31915 raw31915Labels permutation161 permutation4
    mixedMoment B raw31915step0 raw31915step0Labels = mixedMoment B raw31915step1 raw31915step1Labels := by
      have ha : raw31915step1 = -raw31915step0 := by apply Matrix.ext; change ∀ i j, raw31915step1 i j = -(raw31915step0 i j); unfold raw31915step1 raw31915step0; decide +kernel
      have hl : raw31915step1Labels = raw31915step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2192 node2192Labels := by rfl

def raw31916 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw31916Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31916step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw31916step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31916step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw31916step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31916 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31916 raw31916Labels = mixedMoment B node3461 node3461Labels := by
  calc
    mixedMoment B raw31916 raw31916Labels = mixedMoment B raw31916step0 raw31916step0Labels := by
      have ha : raw31916step0 = (fun i j => raw31916 (permutation161 i) (permutation4 j)) := by apply Matrix.ext; unfold raw31916step0 raw31916; decide +kernel
      have hl : raw31916step0Labels = raw31916Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31916 raw31916Labels permutation161 permutation4
    mixedMoment B raw31916step0 raw31916step0Labels = mixedMoment B raw31916step1 raw31916step1Labels := by
      have ha : raw31916step1 = -raw31916step0 := by apply Matrix.ext; change ∀ i j, raw31916step1 i j = -(raw31916step0 i j); unfold raw31916step1 raw31916step0; decide +kernel
      have hl : raw31916step1Labels = raw31916step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3461 node3461Labels := by rfl

def raw31917 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw31917Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31917step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2]]
def raw31917step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31917step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw31917step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31917 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31917 raw31917Labels = mixedMoment B node3601 node3601Labels := by
  calc
    mixedMoment B raw31917 raw31917Labels = mixedMoment B raw31917step0 raw31917step0Labels := by
      have ha : raw31917step0 = (fun i j => raw31917 (permutation160 i) (permutation4 j)) := by apply Matrix.ext; unfold raw31917step0 raw31917; decide +kernel
      have hl : raw31917step0Labels = raw31917Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31917 raw31917Labels permutation160 permutation4
    mixedMoment B raw31917step0 raw31917step0Labels = mixedMoment B raw31917step1 raw31917step1Labels := by
      have ha : raw31917step1 = -raw31917step0 := by apply Matrix.ext; change ∀ i j, raw31917step1 i j = -(raw31917step0 i j); unfold raw31917step1 raw31917step0; decide +kernel
      have hl : raw31917step1Labels = raw31917step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3601 node3601Labels := by rfl

def raw31918 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![2, -2, 0], ![-2, 1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw31918Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31918step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw31918step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31918step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw31918step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31918 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31918 raw31918Labels = mixedMoment B node3559 node3559Labels := by
  calc
    mixedMoment B raw31918 raw31918Labels = mixedMoment B raw31918step0 raw31918step0Labels := by
      have ha : raw31918step0 = (fun i j => raw31918 (permutation203 i) (permutation4 j)) := by apply Matrix.ext; unfold raw31918step0 raw31918; decide +kernel
      have hl : raw31918step0Labels = raw31918Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31918 raw31918Labels permutation203 permutation4
    mixedMoment B raw31918step0 raw31918step0Labels = mixedMoment B raw31918step1 raw31918step1Labels := by
      have ha : raw31918step1 = -raw31918step0 := by apply Matrix.ext; change ∀ i j, raw31918step1 i j = -(raw31918step0 i j); unfold raw31918step1 raw31918step0; decide +kernel
      have hl : raw31918step1Labels = raw31918step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3559 node3559Labels := by rfl

def raw31919 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![2, -2, 0], ![-1, 0, 1], ![-2, 1, 1], ![-1, -1, 2]]
def raw31919Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31919step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw31919step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31919step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw31919step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31919 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31919 raw31919Labels = mixedMoment B node3559 node3559Labels := by
  calc
    mixedMoment B raw31919 raw31919Labels = mixedMoment B raw31919step0 raw31919step0Labels := by
      have ha : raw31919step0 = (fun i j => raw31919 (permutation227 i) (permutation4 j)) := by apply Matrix.ext; unfold raw31919step0 raw31919; decide +kernel
      have hl : raw31919step0Labels = raw31919Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31919 raw31919Labels permutation227 permutation4
    mixedMoment B raw31919step0 raw31919step0Labels = mixedMoment B raw31919step1 raw31919step1Labels := by
      have ha : raw31919step1 = -raw31919step0 := by apply Matrix.ext; change ∀ i j, raw31919step1 i j = -(raw31919step0 i j); unfold raw31919step1 raw31919step0; decide +kernel
      have hl : raw31919step1Labels = raw31919step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3559 node3559Labels := by rfl

def raw31920 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw31920Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31920step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![0, -2, 2], ![-2, 2, 0]]
def raw31920step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31920step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw31920step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31920 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31920 raw31920Labels = mixedMoment B node3600 node3600Labels := by
  calc
    mixedMoment B raw31920 raw31920Labels = mixedMoment B raw31920step0 raw31920step0Labels := by
      have ha : raw31920step0 = (fun i j => raw31920 (permutation161 i) (permutation4 j)) := by apply Matrix.ext; unfold raw31920step0 raw31920; decide +kernel
      have hl : raw31920step0Labels = raw31920Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31920 raw31920Labels permutation161 permutation4
    mixedMoment B raw31920step0 raw31920step0Labels = mixedMoment B raw31920step1 raw31920step1Labels := by
      have ha : raw31920step1 = -raw31920step0 := by apply Matrix.ext; change ∀ i j, raw31920step1 i j = -(raw31920step0 i j); unfold raw31920step1 raw31920step0; decide +kernel
      have hl : raw31920step1Labels = raw31920step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3600 node3600Labels := by rfl

def raw31921 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, -1, 2], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw31921Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31921step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw31921step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31921step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw31921step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31921 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31921 raw31921Labels = mixedMoment B node3782 node3782Labels := by
  calc
    mixedMoment B raw31921 raw31921Labels = mixedMoment B raw31921step0 raw31921step0Labels := by
      have ha : raw31921step0 = (fun i j => raw31921 (permutation662 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31921step0 raw31921; decide +kernel
      have hl : raw31921step0Labels = raw31921Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31921 raw31921Labels permutation662 permutation2
    mixedMoment B raw31921step0 raw31921step0Labels = mixedMoment B raw31921step1 raw31921step1Labels := by
      have ha : raw31921step1 = -raw31921step0 := by apply Matrix.ext; change ∀ i j, raw31921step1 i j = -(raw31921step0 i j); unfold raw31921step1 raw31921step0; decide +kernel
      have hl : raw31921step1Labels = raw31921step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3782 node3782Labels := by rfl

def raw31922 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![-1, -1, 2], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw31922Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31922step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw31922step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31922 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31922 raw31922Labels = mixedMoment B node3170 node3170Labels := by
  calc
    mixedMoment B raw31922 raw31922Labels = mixedMoment B raw31922step0 raw31922step0Labels := by
      have ha : raw31922step0 = (fun i j => raw31922 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31922step0 raw31922; decide +kernel
      have hl : raw31922step0Labels = raw31922Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31922 raw31922Labels permutation178 permutation2
    _ = mixedMoment B node3170 node3170Labels := by rfl

def raw31923 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw31923Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31923step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw31923step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31923 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31923 raw31923Labels = mixedMoment B node3196 node3196Labels := by
  calc
    mixedMoment B raw31923 raw31923Labels = mixedMoment B raw31923step0 raw31923step0Labels := by
      have ha : raw31923step0 = (fun i j => raw31923 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31923step0 raw31923; decide +kernel
      have hl : raw31923step0Labels = raw31923Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31923 raw31923Labels permutation154 permutation2
    _ = mixedMoment B node3196 node3196Labels := by rfl

def raw31924 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, -1, 2], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw31924Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31924step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw31924step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31924 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31924 raw31924Labels = mixedMoment B node3162 node3162Labels := by
  calc
    mixedMoment B raw31924 raw31924Labels = mixedMoment B raw31924step0 raw31924step0Labels := by
      have ha : raw31924step0 = (fun i j => raw31924 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31924step0 raw31924; decide +kernel
      have hl : raw31924step0Labels = raw31924Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31924 raw31924Labels permutation178 permutation2
    _ = mixedMoment B node3162 node3162Labels := by rfl

def raw31925 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, -1, 2], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw31925Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31925step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw31925step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31925 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31925 raw31925Labels = mixedMoment B node3163 node3163Labels := by
  calc
    mixedMoment B raw31925 raw31925Labels = mixedMoment B raw31925step0 raw31925step0Labels := by
      have ha : raw31925step0 = (fun i j => raw31925 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31925step0 raw31925; decide +kernel
      have hl : raw31925step0Labels = raw31925Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31925 raw31925Labels permutation176 permutation2
    _ = mixedMoment B node3163 node3163Labels := by rfl

def raw31926 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, -1, 2], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw31926Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31926step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-3, 3, 0]]
def raw31926step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31926step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw31926step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31926 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31926 raw31926Labels = mixedMoment B node2430 node2430Labels := by
  calc
    mixedMoment B raw31926 raw31926Labels = mixedMoment B raw31926step0 raw31926step0Labels := by
      have ha : raw31926step0 = (fun i j => raw31926 (permutation662 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31926step0 raw31926; decide +kernel
      have hl : raw31926step0Labels = raw31926Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31926 raw31926Labels permutation662 permutation2
    mixedMoment B raw31926step0 raw31926step0Labels = mixedMoment B raw31926step1 raw31926step1Labels := by
      have ha : raw31926step1 = -raw31926step0 := by apply Matrix.ext; change ∀ i j, raw31926step1 i j = -(raw31926step0 i j); unfold raw31926step1 raw31926step0; decide +kernel
      have hl : raw31926step1Labels = raw31926step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2430 node2430Labels := by rfl

def raw31927 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![-2, 2], ![1, -1], ![0, 0], ![2, -2]]
def raw31927Labels : Fin 2 → Fin 2 := ![0, 1]

def raw31927step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![-2, 2], ![1, -1], ![2, -2]]
def raw31927step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw31927step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![1, -1], ![2, -2]]
def raw31927step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw31927step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw31927step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical31927 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31927 raw31927Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw31927 raw31927Labels = mixedMoment B raw31927step0 raw31927step0Labels := by
      have hz : ∀ j, raw31927 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw31927step0 = (fun i j => raw31927 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw31927step0 raw31927; decide +kernel
      have hl : raw31927step0Labels = raw31927Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31927 raw31927Labels permutation520 hz
    mixedMoment B raw31927step0 raw31927step0Labels = mixedMoment B raw31927step1 raw31927step1Labels := by
      have hz : ∀ j, raw31927step0 (permutation32 0) j = 0 := by decide +kernel
      have ha : raw31927step1 = (fun i j => raw31927step0 (permutation32 i.succ) j) := by apply Matrix.ext; unfold raw31927step1 raw31927step0; decide +kernel
      have hl : raw31927step1Labels = raw31927step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31927step0 raw31927step0Labels permutation32 hz
    mixedMoment B raw31927step1 raw31927step1Labels = mixedMoment B raw31927step2 raw31927step2Labels := by
      have ha : raw31927step2 = (fun i j => raw31927step1 (permutation14 i) (permutation0 j)) := by apply Matrix.ext; unfold raw31927step2 raw31927step1; decide +kernel
      have hl : raw31927step2Labels = raw31927step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31927step1 raw31927step1Labels permutation14 permutation0
    _ = mixedMoment B node4092 node4092Labels := by rfl

def raw31928 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw31928Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31928step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw31928step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31928step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw31928step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31928 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31928 raw31928Labels = mixedMoment B node3732 node3732Labels := by
  calc
    mixedMoment B raw31928 raw31928Labels = mixedMoment B raw31928step0 raw31928step0Labels := by
      have hz : ∀ j, raw31928 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31928step0 = (fun i j => raw31928 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31928step0 raw31928; decide +kernel
      have hl : raw31928step0Labels = raw31928Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31928 raw31928Labels permutation346 hz
    mixedMoment B raw31928step0 raw31928step0Labels = mixedMoment B raw31928step1 raw31928step1Labels := by
      have ha : raw31928step1 = (fun i j => raw31928step0 (permutation58 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31928step1 raw31928step0; decide +kernel
      have hl : raw31928step1Labels = raw31928step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31928step0 raw31928step0Labels permutation58 permutation2
    _ = mixedMoment B node3732 node3732Labels := by rfl

def raw31929 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw31929Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31929step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw31929step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31929step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw31929step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31929 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31929 raw31929Labels = mixedMoment B node3180 node3180Labels := by
  calc
    mixedMoment B raw31929 raw31929Labels = mixedMoment B raw31929step0 raw31929step0Labels := by
      have hz : ∀ j, raw31929 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31929step0 = (fun i j => raw31929 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31929step0 raw31929; decide +kernel
      have hl : raw31929step0Labels = raw31929Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31929 raw31929Labels permutation346 hz
    mixedMoment B raw31929step0 raw31929step0Labels = mixedMoment B raw31929step1 raw31929step1Labels := by
      have ha : raw31929step1 = (fun i j => raw31929step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31929step1 raw31929step0; decide +kernel
      have hl : raw31929step1Labels = raw31929step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31929step0 raw31929step0Labels permutation34 permutation2
    _ = mixedMoment B node3180 node3180Labels := by rfl

def raw31930 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, -1, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw31930Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31930step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw31930step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31930 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31930 raw31930Labels = mixedMoment B node3136 node3136Labels := by
  calc
    mixedMoment B raw31930 raw31930Labels = mixedMoment B raw31930step0 raw31930step0Labels := by
      have ha : raw31930step0 = (fun i j => raw31930 (permutation164 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31930step0 raw31930; decide +kernel
      have hl : raw31930step0Labels = raw31930Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31930 raw31930Labels permutation164 permutation2
    _ = mixedMoment B node3136 node3136Labels := by rfl

def raw31931 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, 0, 0], ![2, -1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw31931Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31931step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![2, -1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw31931step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31931step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, -2, 1], ![2, -1, -1], ![2, 0, -2]]
def raw31931step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31931 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31931 raw31931Labels = mixedMoment B node3138 node3138Labels := by
  calc
    mixedMoment B raw31931 raw31931Labels = mixedMoment B raw31931step0 raw31931step0Labels := by
      have hz : ∀ j, raw31931 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31931step0 = (fun i j => raw31931 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31931step0 raw31931; decide +kernel
      have hl : raw31931step0Labels = raw31931Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31931 raw31931Labels permutation346 hz
    mixedMoment B raw31931step0 raw31931step0Labels = mixedMoment B raw31931step1 raw31931step1Labels := by
      have ha : raw31931step1 = (fun i j => raw31931step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31931step1 raw31931step0; decide +kernel
      have hl : raw31931step1Labels = raw31931step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31931step0 raw31931step0Labels permutation34 permutation2
    _ = mixedMoment B node3138 node3138Labels := by rfl

def raw31932 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw31932Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31932step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw31932step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31932step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw31932step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31932 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31932 raw31932Labels = mixedMoment B node3033 node3033Labels := by
  calc
    mixedMoment B raw31932 raw31932Labels = mixedMoment B raw31932step0 raw31932step0Labels := by
      have hz : ∀ j, raw31932 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31932step0 = (fun i j => raw31932 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31932step0 raw31932; decide +kernel
      have hl : raw31932step0Labels = raw31932Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31932 raw31932Labels permutation346 hz
    mixedMoment B raw31932step0 raw31932step0Labels = mixedMoment B raw31932step1 raw31932step1Labels := by
      have ha : raw31932step1 = (fun i j => raw31932step0 (permutation113 i) (permutation4 j)) := by apply Matrix.ext; unfold raw31932step1 raw31932step0; decide +kernel
      have hl : raw31932step1Labels = raw31932step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31932step0 raw31932step0Labels permutation113 permutation4
    _ = mixedMoment B node3033 node3033Labels := by rfl

def raw31933 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![3, -1, -2]]
def raw31933Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31933step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, 0, -1], ![1, -2, 1], ![3, -1, -2]]
def raw31933step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31933step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, -2, 1], ![-2, 0, 2], ![-3, 3, 0]]
def raw31933step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31933step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![2, 0, -2], ![3, -3, 0]]
def raw31933step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31933 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31933 raw31933Labels = mixedMoment B node2443 node2443Labels := by
  calc
    mixedMoment B raw31933 raw31933Labels = mixedMoment B raw31933step0 raw31933step0Labels := by
      have hz : ∀ j, raw31933 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31933step0 = (fun i j => raw31933 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31933step0 raw31933; decide +kernel
      have hl : raw31933step0Labels = raw31933Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31933 raw31933Labels permutation346 hz
    mixedMoment B raw31933step0 raw31933step0Labels = mixedMoment B raw31933step1 raw31933step1Labels := by
      have ha : raw31933step1 = (fun i j => raw31933step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31933step1 raw31933step0; decide +kernel
      have hl : raw31933step1Labels = raw31933step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31933step0 raw31933step0Labels permutation145 permutation2
    mixedMoment B raw31933step1 raw31933step1Labels = mixedMoment B raw31933step2 raw31933step2Labels := by
      have ha : raw31933step2 = -raw31933step1 := by apply Matrix.ext; change ∀ i j, raw31933step2 i j = -(raw31933step1 i j); unfold raw31933step2 raw31933step1; decide +kernel
      have hl : raw31933step2Labels = raw31933step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2443 node2443Labels := by rfl

def raw31934 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![0, 0], ![1, -1], ![-1, 1], ![2, -2]]
def raw31934Labels : Fin 2 → Fin 2 := ![0, 1]

def raw31934step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![1, -1], ![-1, 1], ![2, -2]]
def raw31934step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw31934step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![-1, 1], ![2, -2]]
def raw31934step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw31934step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw31934step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical31934 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31934 raw31934Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw31934 raw31934Labels = mixedMoment B raw31934step0 raw31934step0Labels := by
      have hz : ∀ j, raw31934 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31934step0 = (fun i j => raw31934 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31934step0 raw31934; decide +kernel
      have hl : raw31934step0Labels = raw31934Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31934 raw31934Labels permutation346 hz
    mixedMoment B raw31934step0 raw31934step0Labels = mixedMoment B raw31934step1 raw31934step1Labels := by
      have hz : ∀ j, raw31934step0 (permutation32 0) j = 0 := by decide +kernel
      have ha : raw31934step1 = (fun i j => raw31934step0 (permutation32 i.succ) j) := by apply Matrix.ext; unfold raw31934step1 raw31934step0; decide +kernel
      have hl : raw31934step1Labels = raw31934step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31934step0 raw31934step0Labels permutation32 hz
    mixedMoment B raw31934step1 raw31934step1Labels = mixedMoment B raw31934step2 raw31934step2Labels := by
      have ha : raw31934step2 = (fun i j => raw31934step1 (permutation10 i) (permutation0 j)) := by apply Matrix.ext; unfold raw31934step2 raw31934step1; decide +kernel
      have hl : raw31934step2Labels = raw31934step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31934step1 raw31934step1Labels permutation10 permutation0
    _ = mixedMoment B node4092 node4092Labels := by rfl

def raw31935 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw31935Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31935step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw31935step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31935 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31935 raw31935Labels = mixedMoment B node942 node942Labels := by
  calc
    mixedMoment B raw31935 raw31935Labels = mixedMoment B raw31935step0 raw31935step0Labels := by
      have ha : raw31935step0 = (fun i j => raw31935 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31935step0 raw31935; decide +kernel
      have hl : raw31935step0Labels = raw31935Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31935 raw31935Labels permutation160 permutation2
    _ = mixedMoment B node942 node942Labels := by rfl

def raw31936 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw31936Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31936step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw31936step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31936 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31936 raw31936Labels = mixedMoment B node1822 node1822Labels := by
  calc
    mixedMoment B raw31936 raw31936Labels = mixedMoment B raw31936step0 raw31936step0Labels := by
      have ha : raw31936step0 = (fun i j => raw31936 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31936step0 raw31936; decide +kernel
      have hl : raw31936step0Labels = raw31936Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31936 raw31936Labels permutation160 permutation2
    _ = mixedMoment B node1822 node1822Labels := by rfl

def raw31937 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1]]
def raw31937Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31937step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw31937step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31937step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw31937step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31937 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31937 raw31937Labels = mixedMoment B node2107 node2107Labels := by
  calc
    mixedMoment B raw31937 raw31937Labels = mixedMoment B raw31937step0 raw31937step0Labels := by
      have hz : ∀ j, raw31937 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw31937step0 = (fun i j => raw31937 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw31937step0 raw31937; decide +kernel
      have hl : raw31937step0Labels = raw31937Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31937 raw31937Labels permutation520 hz
    mixedMoment B raw31937step0 raw31937step0Labels = mixedMoment B raw31937step1 raw31937step1Labels := by
      have ha : raw31937step1 = (fun i j => raw31937step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31937step1 raw31937step0; decide +kernel
      have hl : raw31937step1Labels = raw31937step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31937step0 raw31937step0Labels permutation34 permutation2
    _ = mixedMoment B node2107 node2107Labels := by rfl

def raw31938 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw31938Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31938step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw31938step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31938 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31938 raw31938Labels = mixedMoment B node2105 node2105Labels := by
  calc
    mixedMoment B raw31938 raw31938Labels = mixedMoment B raw31938step0 raw31938step0Labels := by
      have ha : raw31938step0 = (fun i j => raw31938 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31938step0 raw31938; decide +kernel
      have hl : raw31938step0Labels = raw31938Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31938 raw31938Labels permutation160 permutation2
    _ = mixedMoment B node2105 node2105Labels := by rfl

def raw31939 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw31939Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31939step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw31939step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31939 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31939 raw31939Labels = mixedMoment B node3721 node3721Labels := by
  calc
    mixedMoment B raw31939 raw31939Labels = mixedMoment B raw31939step0 raw31939step0Labels := by
      have ha : raw31939step0 = (fun i j => raw31939 (permutation265 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31939step0 raw31939; decide +kernel
      have hl : raw31939step0Labels = raw31939Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31939 raw31939Labels permutation265 permutation2
    _ = mixedMoment B node3721 node3721Labels := by rfl

def raw31940 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw31940Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31940 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31940 raw31940Labels = mixedMoment B node3172 node3172Labels := by
  calc
    _ = mixedMoment B node3172 node3172Labels := by rfl

def raw31941 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw31941Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31941 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31941 raw31941Labels = mixedMoment B node3137 node3137Labels := by
  calc
    _ = mixedMoment B node3137 node3137Labels := by rfl

def raw31942 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw31942Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31942step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31942step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31942 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31942 raw31942Labels = mixedMoment B node3135 node3135Labels := by
  calc
    mixedMoment B raw31942 raw31942Labels = mixedMoment B raw31942step0 raw31942step0Labels := by
      have ha : raw31942step0 = (fun i j => raw31942 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31942step0 raw31942; decide +kernel
      have hl : raw31942step0Labels = raw31942Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31942 raw31942Labels permutation154 permutation2
    _ = mixedMoment B node3135 node3135Labels := by rfl

def raw31943 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31943Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31943 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31943 raw31943Labels = mixedMoment B node3135 node3135Labels := by
  calc
    _ = mixedMoment B node3135 node3135Labels := by rfl

def raw31944 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw31944Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31944step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1], ![-2, 0, 2], ![-3, 3, 0]]
def raw31944step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31944step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw31944step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31944 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31944 raw31944Labels = mixedMoment B node2890 node2890Labels := by
  calc
    mixedMoment B raw31944 raw31944Labels = mixedMoment B raw31944step0 raw31944step0Labels := by
      have ha : raw31944step0 = (fun i j => raw31944 (permutation664 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31944step0 raw31944; decide +kernel
      have hl : raw31944step0Labels = raw31944Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31944 raw31944Labels permutation664 permutation2
    mixedMoment B raw31944step0 raw31944step0Labels = mixedMoment B raw31944step1 raw31944step1Labels := by
      have ha : raw31944step1 = -raw31944step0 := by apply Matrix.ext; change ∀ i j, raw31944step1 i j = -(raw31944step0 i j); unfold raw31944step1 raw31944step0; decide +kernel
      have hl : raw31944step1Labels = raw31944step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2890 node2890Labels := by rfl

def raw31945 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw31945Labels : Fin 2 → Fin 2 := ![0, 1]

def raw31945step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw31945step0Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical31945 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31945 raw31945Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw31945 raw31945Labels = mixedMoment B raw31945step0 raw31945step0Labels := by
      have hz : ∀ j, raw31945 (permutation152 0) j = 0 := by decide +kernel
      have ha : raw31945step0 = (fun i j => raw31945 (permutation152 i.succ) j) := by apply Matrix.ext; unfold raw31945step0 raw31945; decide +kernel
      have hl : raw31945step0Labels = raw31945Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31945 raw31945Labels permutation152 hz
    _ = mixedMoment B node4091 node4091Labels := by rfl

def raw31946 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw31946Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31946step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw31946step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31946 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31946 raw31946Labels = mixedMoment B node944 node944Labels := by
  calc
    mixedMoment B raw31946 raw31946Labels = mixedMoment B raw31946step0 raw31946step0Labels := by
      have ha : raw31946step0 = (fun i j => raw31946 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31946step0 raw31946; decide +kernel
      have hl : raw31946step0Labels = raw31946Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31946 raw31946Labels permutation158 permutation2
    _ = mixedMoment B node944 node944Labels := by rfl

def raw31947 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw31947Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31947step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw31947step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31947 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31947 raw31947Labels = mixedMoment B node1824 node1824Labels := by
  calc
    mixedMoment B raw31947 raw31947Labels = mixedMoment B raw31947step0 raw31947step0Labels := by
      have ha : raw31947step0 = (fun i j => raw31947 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31947step0 raw31947; decide +kernel
      have hl : raw31947step0Labels = raw31947Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31947 raw31947Labels permutation158 permutation2
    _ = mixedMoment B node1824 node1824Labels := by rfl

def raw31948 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![0, 1, -1], ![2, -2, 0]]
def raw31948Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31948step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw31948step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31948 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31948 raw31948Labels = mixedMoment B node2089 node2089Labels := by
  calc
    mixedMoment B raw31948 raw31948Labels = mixedMoment B raw31948step0 raw31948step0Labels := by
      have ha : raw31948step0 = (fun i j => raw31948 (permutation166 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31948step0 raw31948; decide +kernel
      have hl : raw31948step0Labels = raw31948Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31948 raw31948Labels permutation166 permutation2
    _ = mixedMoment B node2089 node2089Labels := by rfl

def raw31949 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0]]
def raw31949Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31949step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw31949step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31949 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31949 raw31949Labels = mixedMoment B node2105 node2105Labels := by
  calc
    mixedMoment B raw31949 raw31949Labels = mixedMoment B raw31949step0 raw31949step0Labels := by
      have ha : raw31949step0 = (fun i j => raw31949 (permutation162 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31949step0 raw31949; decide +kernel
      have hl : raw31949step0Labels = raw31949Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31949 raw31949Labels permutation162 permutation2
    _ = mixedMoment B node2105 node2105Labels := by rfl

def raw31950 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw31950Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31950step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw31950step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31950 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31950 raw31950Labels = mixedMoment B node3719 node3719Labels := by
  calc
    mixedMoment B raw31950 raw31950Labels = mixedMoment B raw31950step0 raw31950step0Labels := by
      have ha : raw31950step0 = (fun i j => raw31950 (permutation267 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31950step0 raw31950; decide +kernel
      have hl : raw31950step0Labels = raw31950Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31950 raw31950Labels permutation267 permutation2
    _ = mixedMoment B node3719 node3719Labels := by rfl

def raw31951 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw31951Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31951step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw31951step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31951 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31951 raw31951Labels = mixedMoment B node3170 node3170Labels := by
  calc
    mixedMoment B raw31951 raw31951Labels = mixedMoment B raw31951step0 raw31951step0Labels := by
      have ha : raw31951step0 = (fun i j => raw31951 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31951step0 raw31951; decide +kernel
      have hl : raw31951step0Labels = raw31951Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31951 raw31951Labels permutation154 permutation2
    _ = mixedMoment B node3170 node3170Labels := by rfl

def raw31952 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, -2, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw31952Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31952step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw31952step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31952 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31952 raw31952Labels = mixedMoment B node3136 node3136Labels := by
  calc
    mixedMoment B raw31952 raw31952Labels = mixedMoment B raw31952step0 raw31952step0Labels := by
      have ha : raw31952step0 = (fun i j => raw31952 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31952step0 raw31952; decide +kernel
      have hl : raw31952step0Labels = raw31952Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31952 raw31952Labels permutation154 permutation2
    _ = mixedMoment B node3136 node3136Labels := by rfl

def raw31953 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, -1, 1], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw31953Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31953step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw31953step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31953 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31953 raw31953Labels = mixedMoment B node3133 node3133Labels := by
  calc
    mixedMoment B raw31953 raw31953Labels = mixedMoment B raw31953step0 raw31953step0Labels := by
      have ha : raw31953step0 = (fun i j => raw31953 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31953step0 raw31953; decide +kernel
      have hl : raw31953step0Labels = raw31953Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31953 raw31953Labels permutation154 permutation2
    _ = mixedMoment B node3133 node3133Labels := by rfl

def raw31954 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw31954Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31954 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31954 raw31954Labels = mixedMoment B node3134 node3134Labels := by
  calc
    _ = mixedMoment B node3134 node3134Labels := by rfl

def raw31955 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw31955Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31955step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2], ![-3, 3, 0]]
def raw31955step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31955step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw31955step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31955 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31955 raw31955Labels = mixedMoment B node2423 node2423Labels := by
  calc
    mixedMoment B raw31955 raw31955Labels = mixedMoment B raw31955step0 raw31955step0Labels := by
      have ha : raw31955step0 = (fun i j => raw31955 (permutation664 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31955step0 raw31955; decide +kernel
      have hl : raw31955step0Labels = raw31955Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31955 raw31955Labels permutation664 permutation2
    mixedMoment B raw31955step0 raw31955step0Labels = mixedMoment B raw31955step1 raw31955step1Labels := by
      have ha : raw31955step1 = -raw31955step0 := by apply Matrix.ext; change ∀ i j, raw31955step1 i j = -(raw31955step0 i j); unfold raw31955step1 raw31955step0; decide +kernel
      have hl : raw31955step1Labels = raw31955step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2423 node2423Labels := by rfl

def raw31956 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![-1, 1], ![1, -1], ![0, 0], ![2, -2]]
def raw31956Labels : Fin 2 → Fin 2 := ![0, 1]

def raw31956step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw31956step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw31956step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw31956step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical31956 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31956 raw31956Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw31956 raw31956Labels = mixedMoment B raw31956step0 raw31956step0Labels := by
      have hz : ∀ j, raw31956 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw31956step0 = (fun i j => raw31956 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw31956step0 raw31956; decide +kernel
      have hl : raw31956step0Labels = raw31956Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31956 raw31956Labels permutation520 hz
    mixedMoment B raw31956step0 raw31956step0Labels = mixedMoment B raw31956step1 raw31956step1Labels := by
      have hz : ∀ j, raw31956step0 (permutation32 0) j = 0 := by decide +kernel
      have ha : raw31956step1 = (fun i j => raw31956step0 (permutation32 i.succ) j) := by apply Matrix.ext; unfold raw31956step1 raw31956step0; decide +kernel
      have hl : raw31956step1Labels = raw31956step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31956step0 raw31956step0Labels permutation32 hz
    _ = mixedMoment B node4092 node4092Labels := by rfl

def raw31957 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw31957Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31957 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31957 raw31957Labels = mixedMoment B node3165 node3165Labels := by
  calc
    _ = mixedMoment B node3165 node3165Labels := by rfl

def raw31958 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw31958Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31958step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw31958step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31958 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31958 raw31958Labels = mixedMoment B node3713 node3713Labels := by
  calc
    mixedMoment B raw31958 raw31958Labels = mixedMoment B raw31958step0 raw31958step0Labels := by
      have ha : raw31958step0 = (fun i j => raw31958 (permutation265 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31958step0 raw31958; decide +kernel
      have hl : raw31958step0Labels = raw31958Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31958 raw31958Labels permutation265 permutation2
    _ = mixedMoment B node3713 node3713Labels := by rfl

def raw31959 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw31959Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31959step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, 0, -1], ![-1, -1, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw31959step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31959step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def raw31959step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31959 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31959 raw31959Labels = mixedMoment B node3778 node3778Labels := by
  calc
    mixedMoment B raw31959 raw31959Labels = mixedMoment B raw31959step0 raw31959step0Labels := by
      have ha : raw31959step0 = (fun i j => raw31959 (permutation662 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31959step0 raw31959; decide +kernel
      have hl : raw31959step0Labels = raw31959Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31959 raw31959Labels permutation662 permutation2
    mixedMoment B raw31959step0 raw31959step0Labels = mixedMoment B raw31959step1 raw31959step1Labels := by
      have ha : raw31959step1 = -raw31959step0 := by apply Matrix.ext; change ∀ i j, raw31959step1 i j = -(raw31959step0 i j); unfold raw31959step1 raw31959step0; decide +kernel
      have hl : raw31959step1Labels = raw31959step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3778 node3778Labels := by rfl

def raw31960 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw31960Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31960step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw31960step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31960 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31960 raw31960Labels = mixedMoment B node3762 node3762Labels := by
  calc
    mixedMoment B raw31960 raw31960Labels = mixedMoment B raw31960step0 raw31960step0Labels := by
      have ha : raw31960step0 = (fun i j => raw31960 (permutation378 i) (permutation4 j)) := by apply Matrix.ext; unfold raw31960step0 raw31960; decide +kernel
      have hl : raw31960step0Labels = raw31960Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31960 raw31960Labels permutation378 permutation4
    _ = mixedMoment B node3762 node3762Labels := by rfl

def raw31961 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -2, 2], ![1, 0, -1], ![0, 1, -1], ![2, 0, -2]]
def raw31961Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31961step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw31961step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31961 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31961 raw31961Labels = mixedMoment B node3762 node3762Labels := by
  calc
    mixedMoment B raw31961 raw31961Labels = mixedMoment B raw31961step0 raw31961step0Labels := by
      have ha : raw31961step0 = (fun i j => raw31961 (permutation374 i) (permutation4 j)) := by apply Matrix.ext; unfold raw31961step0 raw31961; decide +kernel
      have hl : raw31961step0Labels = raw31961Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31961 raw31961Labels permutation374 permutation4
    _ = mixedMoment B node3762 node3762Labels := by rfl

def raw31962 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw31962Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31962step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw31962step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31962 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31962 raw31962Labels = mixedMoment B node3759 node3759Labels := by
  calc
    mixedMoment B raw31962 raw31962Labels = mixedMoment B raw31962step0 raw31962step0Labels := by
      have ha : raw31962step0 = (fun i j => raw31962 (permutation373 i) (permutation4 j)) := by apply Matrix.ext; unfold raw31962step0 raw31962; decide +kernel
      have hl : raw31962step0Labels = raw31962Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31962 raw31962Labels permutation373 permutation4
    _ = mixedMoment B node3759 node3759Labels := by rfl

def raw31963 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]
def raw31963Labels : Fin 2 → Fin 2 := ![0, 1]

def raw31963step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]
def raw31963step0Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical31963 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31963 raw31963Labels = mixedMoment B node4088 node4088Labels := by
  calc
    mixedMoment B raw31963 raw31963Labels = mixedMoment B raw31963step0 raw31963step0Labels := by
      have hz : ∀ j, raw31963 (permutation152 0) j = 0 := by decide +kernel
      have ha : raw31963step0 = (fun i j => raw31963 (permutation152 i.succ) j) := by apply Matrix.ext; unfold raw31963step0 raw31963; decide +kernel
      have hl : raw31963step0Labels = raw31963Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31963 raw31963Labels permutation152 hz
    _ = mixedMoment B node4088 node4088Labels := by rfl

def raw31964 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw31964Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31964step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw31964step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31964step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw31964step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31964 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31964 raw31964Labels = mixedMoment B node3394 node3394Labels := by
  calc
    mixedMoment B raw31964 raw31964Labels = mixedMoment B raw31964step0 raw31964step0Labels := by
      have hz : ∀ j, raw31964 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31964step0 = (fun i j => raw31964 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31964step0 raw31964; decide +kernel
      have hl : raw31964step0Labels = raw31964Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31964 raw31964Labels permutation346 hz
    mixedMoment B raw31964step0 raw31964step0Labels = mixedMoment B raw31964step1 raw31964step1Labels := by
      have ha : raw31964step1 = (fun i j => raw31964step0 (permutation56 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31964step1 raw31964step0; decide +kernel
      have hl : raw31964step1Labels = raw31964step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31964step0 raw31964step0Labels permutation56 permutation2
    _ = mixedMoment B node3394 node3394Labels := by rfl

def raw31965 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw31965Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31965step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw31965step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31965 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31965 raw31965Labels = mixedMoment B node3158 node3158Labels := by
  calc
    mixedMoment B raw31965 raw31965Labels = mixedMoment B raw31965step0 raw31965step0Labels := by
      have hz : ∀ j, raw31965 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31965step0 = (fun i j => raw31965 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31965step0 raw31965; decide +kernel
      have hl : raw31965step0Labels = raw31965Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31965 raw31965Labels permutation346 hz
    _ = mixedMoment B node3158 node3158Labels := by rfl

def raw31966 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw31966Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31966 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31966 raw31966Labels = mixedMoment B node3128 node3128Labels := by
  calc
    _ = mixedMoment B node3128 node3128Labels := by rfl

def raw31967 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw31967Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31967step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw31967step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31967step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31967step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31967 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31967 raw31967Labels = mixedMoment B node3132 node3132Labels := by
  calc
    mixedMoment B raw31967 raw31967Labels = mixedMoment B raw31967step0 raw31967step0Labels := by
      have hz : ∀ j, raw31967 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31967step0 = (fun i j => raw31967 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31967step0 raw31967; decide +kernel
      have hl : raw31967step0Labels = raw31967Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31967 raw31967Labels permutation346 hz
    mixedMoment B raw31967step0 raw31967step0Labels = mixedMoment B raw31967step1 raw31967step1Labels := by
      have ha : raw31967step1 = (fun i j => raw31967step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31967step1 raw31967step0; decide +kernel
      have hl : raw31967step1Labels = raw31967step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31967step0 raw31967step0Labels permutation34 permutation2
    _ = mixedMoment B node3132 node3132Labels := by rfl

def raw31968 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31968Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31968step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31968step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31968 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31968 raw31968Labels = mixedMoment B node3132 node3132Labels := by
  calc
    mixedMoment B raw31968 raw31968Labels = mixedMoment B raw31968step0 raw31968step0Labels := by
      have hz : ∀ j, raw31968 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31968step0 = (fun i j => raw31968 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31968step0 raw31968; decide +kernel
      have hl : raw31968step0Labels = raw31968Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31968 raw31968Labels permutation346 hz
    _ = mixedMoment B node3132 node3132Labels := by rfl

def raw31969 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw31969Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31969step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw31969step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31969step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![1, 0, -1], ![1, 0, -1], ![-2, -1, 3], ![-3, 3, 0]]
def raw31969step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31969step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![2, 1, -3], ![3, -3, 0]]
def raw31969step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31969 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31969 raw31969Labels = mixedMoment B node2899 node2899Labels := by
  calc
    mixedMoment B raw31969 raw31969Labels = mixedMoment B raw31969step0 raw31969step0Labels := by
      have hz : ∀ j, raw31969 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31969step0 = (fun i j => raw31969 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31969step0 raw31969; decide +kernel
      have hl : raw31969step0Labels = raw31969Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31969 raw31969Labels permutation346 hz
    mixedMoment B raw31969step0 raw31969step0Labels = mixedMoment B raw31969step1 raw31969step1Labels := by
      have ha : raw31969step1 = (fun i j => raw31969step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31969step1 raw31969step0; decide +kernel
      have hl : raw31969step1Labels = raw31969step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31969step0 raw31969step0Labels permutation145 permutation2
    mixedMoment B raw31969step1 raw31969step1Labels = mixedMoment B raw31969step2 raw31969step2Labels := by
      have ha : raw31969step2 = -raw31969step1 := by apply Matrix.ext; change ∀ i j, raw31969step2 i j = -(raw31969step1 i j); unfold raw31969step2 raw31969step1; decide +kernel
      have hl : raw31969step2Labels = raw31969step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2899 node2899Labels := by rfl

def raw31970 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![-3, 3], ![0, 0], ![1, -1], ![1, -1], ![1, -1]]
def raw31970Labels : Fin 2 → Fin 2 := ![0, 1]

def raw31970step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-3, 3], ![1, -1], ![1, -1], ![1, -1]]
def raw31970step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw31970step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]
def raw31970step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical31970 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31970 raw31970Labels = mixedMoment B node4083 node4083Labels := by
  calc
    mixedMoment B raw31970 raw31970Labels = mixedMoment B raw31970step0 raw31970step0Labels := by
      have hz : ∀ j, raw31970 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31970step0 = (fun i j => raw31970 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31970step0 raw31970; decide +kernel
      have hl : raw31970step0Labels = raw31970Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31970 raw31970Labels permutation346 hz
    mixedMoment B raw31970step0 raw31970step0Labels = mixedMoment B raw31970step1 raw31970step1Labels := by
      have hz : ∀ j, raw31970step0 (permutation32 0) j = 0 := by decide +kernel
      have ha : raw31970step1 = (fun i j => raw31970step0 (permutation32 i.succ) j) := by apply Matrix.ext; unfold raw31970step1 raw31970step0; decide +kernel
      have hl : raw31970step1Labels = raw31970step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31970step0 raw31970step0Labels permutation32 hz
    _ = mixedMoment B node4083 node4083Labels := by rfl

def raw31971 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw31971Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31971step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw31971step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31971step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw31971step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31971 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31971 raw31971Labels = mixedMoment B node3391 node3391Labels := by
  calc
    mixedMoment B raw31971 raw31971Labels = mixedMoment B raw31971step0 raw31971step0Labels := by
      have hz : ∀ j, raw31971 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31971step0 = (fun i j => raw31971 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31971step0 raw31971; decide +kernel
      have hl : raw31971step0Labels = raw31971Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31971 raw31971Labels permutation346 hz
    mixedMoment B raw31971step0 raw31971step0Labels = mixedMoment B raw31971step1 raw31971step1Labels := by
      have ha : raw31971step1 = (fun i j => raw31971step0 (permutation58 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31971step1 raw31971step0; decide +kernel
      have hl : raw31971step1Labels = raw31971step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31971step0 raw31971step0Labels permutation58 permutation2
    _ = mixedMoment B node3391 node3391Labels := by rfl

def raw31972 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw31972Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31972step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw31972step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31972step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw31972step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31972 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31972 raw31972Labels = mixedMoment B node3156 node3156Labels := by
  calc
    mixedMoment B raw31972 raw31972Labels = mixedMoment B raw31972step0 raw31972step0Labels := by
      have hz : ∀ j, raw31972 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31972step0 = (fun i j => raw31972 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31972step0 raw31972; decide +kernel
      have hl : raw31972step0Labels = raw31972Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31972 raw31972Labels permutation346 hz
    mixedMoment B raw31972step0 raw31972step0Labels = mixedMoment B raw31972step1 raw31972step1Labels := by
      have ha : raw31972step1 = (fun i j => raw31972step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31972step1 raw31972step0; decide +kernel
      have hl : raw31972step1Labels = raw31972step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31972step0 raw31972step0Labels permutation34 permutation2
    _ = mixedMoment B node3156 node3156Labels := by rfl

def raw31973 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw31973Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31973step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw31973step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31973 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31973 raw31973Labels = mixedMoment B node3127 node3127Labels := by
  calc
    mixedMoment B raw31973 raw31973Labels = mixedMoment B raw31973step0 raw31973step0Labels := by
      have ha : raw31973step0 = (fun i j => raw31973 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31973step0 raw31973; decide +kernel
      have hl : raw31973step0Labels = raw31973Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31973 raw31973Labels permutation154 permutation2
    _ = mixedMoment B node3127 node3127Labels := by rfl

def raw31974 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![0, 0, 0], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw31974Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31974step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw31974step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31974step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw31974step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31974 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31974 raw31974Labels = mixedMoment B node3129 node3129Labels := by
  calc
    mixedMoment B raw31974 raw31974Labels = mixedMoment B raw31974step0 raw31974step0Labels := by
      have hz : ∀ j, raw31974 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31974step0 = (fun i j => raw31974 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31974step0 raw31974; decide +kernel
      have hl : raw31974step0Labels = raw31974Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31974 raw31974Labels permutation346 hz
    mixedMoment B raw31974step0 raw31974step0Labels = mixedMoment B raw31974step1 raw31974step1Labels := by
      have ha : raw31974step1 = (fun i j => raw31974step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31974step1 raw31974step0; decide +kernel
      have hl : raw31974step1Labels = raw31974step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31974step0 raw31974step0Labels permutation34 permutation2
    _ = mixedMoment B node3129 node3129Labels := by rfl

def raw31975 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw31975Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31975step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw31975step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31975 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31975 raw31975Labels = mixedMoment B node3131 node3131Labels := by
  calc
    mixedMoment B raw31975 raw31975Labels = mixedMoment B raw31975step0 raw31975step0Labels := by
      have hz : ∀ j, raw31975 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31975step0 = (fun i j => raw31975 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31975step0 raw31975; decide +kernel
      have hl : raw31975step0Labels = raw31975Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31975 raw31975Labels permutation346 hz
    _ = mixedMoment B node3131 node3131Labels := by rfl

def raw31976 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw31976Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31976step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw31976step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31976step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, -1, 0], ![-2, -1, 3], ![-3, 3, 0]]
def raw31976step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31976step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![2, 1, -3], ![3, -3, 0]]
def raw31976step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31976 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31976 raw31976Labels = mixedMoment B node2435 node2435Labels := by
  calc
    mixedMoment B raw31976 raw31976Labels = mixedMoment B raw31976step0 raw31976step0Labels := by
      have hz : ∀ j, raw31976 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31976step0 = (fun i j => raw31976 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31976step0 raw31976; decide +kernel
      have hl : raw31976step0Labels = raw31976Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31976 raw31976Labels permutation346 hz
    mixedMoment B raw31976step0 raw31976step0Labels = mixedMoment B raw31976step1 raw31976step1Labels := by
      have ha : raw31976step1 = (fun i j => raw31976step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31976step1 raw31976step0; decide +kernel
      have hl : raw31976step1Labels = raw31976step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31976step0 raw31976step0Labels permutation145 permutation2
    mixedMoment B raw31976step1 raw31976step1Labels = mixedMoment B raw31976step2 raw31976step2Labels := by
      have ha : raw31976step2 = -raw31976step1 := by apply Matrix.ext; change ∀ i j, raw31976step2 i j = -(raw31976step1 i j); unfold raw31976step2 raw31976step1; decide +kernel
      have hl : raw31976step2Labels = raw31976step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2435 node2435Labels := by rfl

def raw31977 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![-3, 3], ![0, 0], ![1, -1], ![0, 0], ![2, -2]]
def raw31977Labels : Fin 2 → Fin 2 := ![0, 1]

def raw31977step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-3, 3], ![0, 0], ![1, -1], ![2, -2]]
def raw31977step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw31977step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![0, 0], ![-3, 3], ![1, -1], ![2, -2]]
def raw31977step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw31977step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]
def raw31977step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical31977 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31977 raw31977Labels = mixedMoment B node4084 node4084Labels := by
  calc
    mixedMoment B raw31977 raw31977Labels = mixedMoment B raw31977step0 raw31977step0Labels := by
      have hz : ∀ j, raw31977 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw31977step0 = (fun i j => raw31977 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw31977step0 raw31977; decide +kernel
      have hl : raw31977step0Labels = raw31977Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31977 raw31977Labels permutation520 hz
    mixedMoment B raw31977step0 raw31977step0Labels = mixedMoment B raw31977step1 raw31977step1Labels := by
      have hz : ∀ j, raw31977step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31977step1 = (fun i j => raw31977step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31977step1 raw31977step0; decide +kernel
      have hl : raw31977step1Labels = raw31977step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31977step0 raw31977step0Labels permutation80 hz
    mixedMoment B raw31977step1 raw31977step1Labels = mixedMoment B raw31977step2 raw31977step2Labels := by
      have hz : ∀ j, raw31977step1 (permutation8 0) j = 0 := by decide +kernel
      have ha : raw31977step2 = (fun i j => raw31977step1 (permutation8 i.succ) j) := by apply Matrix.ext; unfold raw31977step2 raw31977step1; decide +kernel
      have hl : raw31977step2Labels = raw31977step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31977step1 raw31977step1Labels permutation8 hz
    _ = mixedMoment B node4084 node4084Labels := by rfl

def raw31978 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw31978Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31978step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw31978step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31978 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31978 raw31978Labels = mixedMoment B node1130 node1130Labels := by
  calc
    mixedMoment B raw31978 raw31978Labels = mixedMoment B raw31978step0 raw31978step0Labels := by
      have ha : raw31978step0 = (fun i j => raw31978 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31978step0 raw31978; decide +kernel
      have hl : raw31978step0Labels = raw31978Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31978 raw31978Labels permutation158 permutation2
    _ = mixedMoment B node1130 node1130Labels := by rfl

def raw31979 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw31979Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31979step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw31979step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31979 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31979 raw31979Labels = mixedMoment B node2333 node2333Labels := by
  calc
    mixedMoment B raw31979 raw31979Labels = mixedMoment B raw31979step0 raw31979step0Labels := by
      have ha : raw31979step0 = (fun i j => raw31979 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31979step0 raw31979; decide +kernel
      have hl : raw31979step0Labels = raw31979Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31979 raw31979Labels permutation158 permutation2
    _ = mixedMoment B node2333 node2333Labels := by rfl

def raw31980 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw31980Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31980 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31980 raw31980Labels = mixedMoment B node2481 node2481Labels := by
  calc
    _ = mixedMoment B node2481 node2481Labels := by rfl

def raw31981 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw31981Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31981step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw31981step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31981 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31981 raw31981Labels = mixedMoment B node2515 node2515Labels := by
  calc
    mixedMoment B raw31981 raw31981Labels = mixedMoment B raw31981step0 raw31981step0Labels := by
      have hz : ∀ j, raw31981 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31981step0 = (fun i j => raw31981 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31981step0 raw31981; decide +kernel
      have hl : raw31981step0Labels = raw31981Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31981 raw31981Labels permutation434 hz
    _ = mixedMoment B node2515 node2515Labels := by rfl

def raw31982 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![0, 2, -2], ![2, -2, 0]]
def raw31982Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31982step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw31982step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31982 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31982 raw31982Labels = mixedMoment B node2494 node2494Labels := by
  calc
    mixedMoment B raw31982 raw31982Labels = mixedMoment B raw31982step0 raw31982step0Labels := by
      have ha : raw31982step0 = (fun i j => raw31982 (permutation166 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31982step0 raw31982; decide +kernel
      have hl : raw31982step0Labels = raw31982Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31982 raw31982Labels permutation166 permutation2
    _ = mixedMoment B node2494 node2494Labels := by rfl

def raw31983 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0]]
def raw31983Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31983step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw31983step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31983 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31983 raw31983Labels = mixedMoment B node2508 node2508Labels := by
  calc
    mixedMoment B raw31983 raw31983Labels = mixedMoment B raw31983step0 raw31983step0Labels := by
      have ha : raw31983step0 = (fun i j => raw31983 (permutation162 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31983step0 raw31983; decide +kernel
      have hl : raw31983step0Labels = raw31983Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31983 raw31983Labels permutation162 permutation2
    _ = mixedMoment B node2508 node2508Labels := by rfl

def raw31984 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 0, 1], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw31984Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31984step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw31984step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31984step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw31984step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31984 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31984 raw31984Labels = mixedMoment B node3787 node3787Labels := by
  calc
    mixedMoment B raw31984 raw31984Labels = mixedMoment B raw31984step0 raw31984step0Labels := by
      have ha : raw31984step0 = (fun i j => raw31984 (permutation662 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31984step0 raw31984; decide +kernel
      have hl : raw31984step0Labels = raw31984Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31984 raw31984Labels permutation662 permutation2
    mixedMoment B raw31984step0 raw31984step0Labels = mixedMoment B raw31984step1 raw31984step1Labels := by
      have ha : raw31984step1 = -raw31984step0 := by apply Matrix.ext; change ∀ i j, raw31984step1 i j = -(raw31984step0 i j); unfold raw31984step1 raw31984step0; decide +kernel
      have hl : raw31984step1Labels = raw31984step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3787 node3787Labels := by rfl

def raw31985 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw31985Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31985step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw31985step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31985 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31985 raw31985Labels = mixedMoment B node2984 node2984Labels := by
  calc
    mixedMoment B raw31985 raw31985Labels = mixedMoment B raw31985step0 raw31985step0Labels := by
      have ha : raw31985step0 = (fun i j => raw31985 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31985step0 raw31985; decide +kernel
      have hl : raw31985step0Labels = raw31985Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31985 raw31985Labels permutation154 permutation2
    _ = mixedMoment B node2984 node2984Labels := by rfl

def raw31986 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![-1, 0, 1], ![2, -1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw31986Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31986step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -2, 1], ![2, -1, -1], ![2, 0, -2]]
def raw31986step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31986 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31986 raw31986Labels = mixedMoment B node2900 node2900Labels := by
  calc
    mixedMoment B raw31986 raw31986Labels = mixedMoment B raw31986step0 raw31986step0Labels := by
      have ha : raw31986step0 = (fun i j => raw31986 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31986step0 raw31986; decide +kernel
      have hl : raw31986step0Labels = raw31986Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31986 raw31986Labels permutation178 permutation2
    _ = mixedMoment B node2900 node2900Labels := by rfl

def raw31987 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw31987Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31987step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw31987step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31987 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31987 raw31987Labels = mixedMoment B node2902 node2902Labels := by
  calc
    mixedMoment B raw31987 raw31987Labels = mixedMoment B raw31987step0 raw31987step0Labels := by
      have ha : raw31987step0 = (fun i j => raw31987 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31987step0 raw31987; decide +kernel
      have hl : raw31987step0Labels = raw31987Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31987 raw31987Labels permutation176 permutation2
    _ = mixedMoment B node2902 node2902Labels := by rfl

def raw31988 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![-1, 0, 1], ![1, 0, -1], ![1, -2, 1], ![3, -1, -2]]
def raw31988Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31988step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 2, 1]]
def raw31988step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31988step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw31988step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31988 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31988 raw31988Labels = mixedMoment B node2437 node2437Labels := by
  calc
    mixedMoment B raw31988 raw31988Labels = mixedMoment B raw31988step0 raw31988step0Labels := by
      have ha : raw31988step0 = (fun i j => raw31988 (permutation662 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31988step0 raw31988; decide +kernel
      have hl : raw31988step0Labels = raw31988Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31988 raw31988Labels permutation662 permutation2
    mixedMoment B raw31988step0 raw31988step0Labels = mixedMoment B raw31988step1 raw31988step1Labels := by
      have ha : raw31988step1 = -raw31988step0 := by apply Matrix.ext; change ∀ i j, raw31988step1 i j = -(raw31988step0 i j); unfold raw31988step1 raw31988step0; decide +kernel
      have hl : raw31988step1Labels = raw31988step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2437 node2437Labels := by rfl

def raw31989 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 2, -1], ![1, -1, 0], ![-1, 0, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw31989Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31989step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw31989step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31989step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw31989step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31989 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31989 raw31989Labels = mixedMoment B node3501 node3501Labels := by
  calc
    mixedMoment B raw31989 raw31989Labels = mixedMoment B raw31989step0 raw31989step0Labels := by
      have ha : raw31989step0 = (fun i j => raw31989 (permutation188 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31989step0 raw31989; decide +kernel
      have hl : raw31989step0Labels = raw31989Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31989 raw31989Labels permutation188 permutation2
    mixedMoment B raw31989step0 raw31989step0Labels = mixedMoment B raw31989step1 raw31989step1Labels := by
      have ha : raw31989step1 = -raw31989step0 := by apply Matrix.ext; change ∀ i j, raw31989step1 i j = -(raw31989step0 i j); unfold raw31989step1 raw31989step0; decide +kernel
      have hl : raw31989step1Labels = raw31989step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3501 node3501Labels := by rfl

def raw31990 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw31990Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31990step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![-1, 0, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw31990step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31990step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw31990step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31990step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw31990step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31990 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31990 raw31990Labels = mixedMoment B node3564 node3564Labels := by
  calc
    mixedMoment B raw31990 raw31990Labels = mixedMoment B raw31990step0 raw31990step0Labels := by
      have hz : ∀ j, raw31990 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31990step0 = (fun i j => raw31990 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31990step0 raw31990; decide +kernel
      have hl : raw31990step0Labels = raw31990Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31990 raw31990Labels permutation346 hz
    mixedMoment B raw31990step0 raw31990step0Labels = mixedMoment B raw31990step1 raw31990step1Labels := by
      have ha : raw31990step1 = (fun i j => raw31990step0 (permutation44 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31990step1 raw31990step0; decide +kernel
      have hl : raw31990step1Labels = raw31990step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31990step0 raw31990step0Labels permutation44 permutation2
    mixedMoment B raw31990step1 raw31990step1Labels = mixedMoment B raw31990step2 raw31990step2Labels := by
      have ha : raw31990step2 = -raw31990step1 := by apply Matrix.ext; change ∀ i j, raw31990step2 i j = -(raw31990step1 i j); unfold raw31990step2 raw31990step1; decide +kernel
      have hl : raw31990step2Labels = raw31990step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3564 node3564Labels := by rfl

def raw31991 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![1, -1, 0], ![-2, 1, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw31991Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31991step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -2, 1], ![0, 1, -1], ![-2, 1, 1], ![-2, 0, 2]]
def raw31991step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31991step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw31991step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31991 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31991 raw31991Labels = mixedMoment B node3499 node3499Labels := by
  calc
    mixedMoment B raw31991 raw31991Labels = mixedMoment B raw31991step0 raw31991step0Labels := by
      have ha : raw31991step0 = (fun i j => raw31991 (permutation188 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31991step0 raw31991; decide +kernel
      have hl : raw31991step0Labels = raw31991Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31991 raw31991Labels permutation188 permutation2
    mixedMoment B raw31991step0 raw31991step0Labels = mixedMoment B raw31991step1 raw31991step1Labels := by
      have ha : raw31991step1 = -raw31991step0 := by apply Matrix.ext; change ∀ i j, raw31991step1 i j = -(raw31991step0 i j); unfold raw31991step1 raw31991step0; decide +kernel
      have hl : raw31991step1Labels = raw31991step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3499 node3499Labels := by rfl

def raw31992 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw31992Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31992step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw31992step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31992step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw31992step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31992 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31992 raw31992Labels = mixedMoment B node3514 node3514Labels := by
  calc
    mixedMoment B raw31992 raw31992Labels = mixedMoment B raw31992step0 raw31992step0Labels := by
      have ha : raw31992step0 = (fun i j => raw31992 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31992step0 raw31992; decide +kernel
      have hl : raw31992step0Labels = raw31992Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31992 raw31992Labels permutation178 permutation2
    mixedMoment B raw31992step0 raw31992step0Labels = mixedMoment B raw31992step1 raw31992step1Labels := by
      have ha : raw31992step1 = -raw31992step0 := by apply Matrix.ext; change ∀ i j, raw31992step1 i j = -(raw31992step0 i j); unfold raw31992step1 raw31992step0; decide +kernel
      have hl : raw31992step1Labels = raw31992step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3514 node3514Labels := by rfl

def raw31993 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![1, -1, 0], ![-1, 0, 1], ![1, -2, 1], ![-3, 1, 2]]
def raw31993Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31993step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw31993step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31993 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31993 raw31993Labels = mixedMoment B node2476 node2476Labels := by
  calc
    mixedMoment B raw31993 raw31993Labels = mixedMoment B raw31993step0 raw31993step0Labels := by
      have ha : raw31993step0 = (fun i j => raw31993 (permutation654 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31993step0 raw31993; decide +kernel
      have hl : raw31993step0Labels = raw31993Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31993 raw31993Labels permutation654 permutation2
    _ = mixedMoment B node2476 node2476Labels := by rfl

def raw31994 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw31994Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31994step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw31994step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31994 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31994 raw31994Labels = mixedMoment B node1127 node1127Labels := by
  calc
    mixedMoment B raw31994 raw31994Labels = mixedMoment B raw31994step0 raw31994step0Labels := by
      have ha : raw31994step0 = (fun i j => raw31994 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31994step0 raw31994; decide +kernel
      have hl : raw31994step0Labels = raw31994Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31994 raw31994Labels permutation160 permutation2
    _ = mixedMoment B node1127 node1127Labels := by rfl

def raw31995 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw31995Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31995step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw31995step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31995 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31995 raw31995Labels = mixedMoment B node2331 node2331Labels := by
  calc
    mixedMoment B raw31995 raw31995Labels = mixedMoment B raw31995step0 raw31995step0Labels := by
      have ha : raw31995step0 = (fun i j => raw31995 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31995step0 raw31995; decide +kernel
      have hl : raw31995step0Labels = raw31995Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31995 raw31995Labels permutation160 permutation2
    _ = mixedMoment B node2331 node2331Labels := by rfl

def raw31996 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw31996Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31996step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw31996step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31996step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw31996step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31996 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31996 raw31996Labels = mixedMoment B node2512 node2512Labels := by
  calc
    mixedMoment B raw31996 raw31996Labels = mixedMoment B raw31996step0 raw31996step0Labels := by
      have hz : ∀ j, raw31996 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31996step0 = (fun i j => raw31996 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31996step0 raw31996; decide +kernel
      have hl : raw31996step0Labels = raw31996Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31996 raw31996Labels permutation434 hz
    mixedMoment B raw31996step0 raw31996step0Labels = mixedMoment B raw31996step1 raw31996step1Labels := by
      have ha : raw31996step1 = (fun i j => raw31996step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31996step1 raw31996step0; decide +kernel
      have hl : raw31996step1Labels = raw31996step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31996step0 raw31996step0Labels permutation34 permutation2
    _ = mixedMoment B node2512 node2512Labels := by rfl

def raw31997 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1]]
def raw31997Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31997step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw31997step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31997step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw31997step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31997 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31997 raw31997Labels = mixedMoment B node2512 node2512Labels := by
  calc
    mixedMoment B raw31997 raw31997Labels = mixedMoment B raw31997step0 raw31997step0Labels := by
      have hz : ∀ j, raw31997 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw31997step0 = (fun i j => raw31997 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw31997step0 raw31997; decide +kernel
      have hl : raw31997step0Labels = raw31997Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31997 raw31997Labels permutation520 hz
    mixedMoment B raw31997step0 raw31997step0Labels = mixedMoment B raw31997step1 raw31997step1Labels := by
      have ha : raw31997step1 = (fun i j => raw31997step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31997step1 raw31997step0; decide +kernel
      have hl : raw31997step1Labels = raw31997step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31997step0 raw31997step0Labels permutation34 permutation2
    _ = mixedMoment B node2512 node2512Labels := by rfl

def raw31998 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw31998Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31998step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw31998step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31998 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31998 raw31998Labels = mixedMoment B node3945 node3945Labels := by
  calc
    mixedMoment B raw31998 raw31998Labels = mixedMoment B raw31998step0 raw31998step0Labels := by
      have ha : raw31998step0 = (fun i j => raw31998 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31998step0 raw31998; decide +kernel
      have hl : raw31998step0Labels = raw31998Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31998 raw31998Labels permutation176 permutation2
    _ = mixedMoment B node3945 node3945Labels := by rfl

def raw31999 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![-1, -1, 2], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw31999Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31999step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31999step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31999 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31999 raw31999Labels = mixedMoment B node2849 node2849Labels := by
  calc
    mixedMoment B raw31999 raw31999Labels = mixedMoment B raw31999step0 raw31999step0Labels := by
      have ha : raw31999step0 = (fun i j => raw31999 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31999step0 raw31999; decide +kernel
      have hl : raw31999step0Labels = raw31999Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31999 raw31999Labels permutation178 permutation2
    _ = mixedMoment B node2849 node2849Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
