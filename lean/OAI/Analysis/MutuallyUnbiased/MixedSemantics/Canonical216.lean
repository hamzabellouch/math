import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes11
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes14
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes28
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes29
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes30
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes66
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes73
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes74
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw27648 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw27648Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27648step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw27648step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27648step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27648step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw27648step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27648step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27648 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27648 raw27648Labels = mixedMoment B node4807 node4807Labels := by
  calc
    mixedMoment B raw27648 raw27648Labels = mixedMoment B raw27648step0 raw27648step0Labels := by
      have hz : ∀ j, raw27648 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27648step0 = (fun i j => raw27648 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27648step0 raw27648; decide +kernel
      have hl : raw27648step0Labels = raw27648Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27648 raw27648Labels permutation434 hz
    mixedMoment B raw27648step0 raw27648step0Labels = mixedMoment B raw27648step1 raw27648step1Labels := by
      have ha : raw27648step1 = (fun i j => raw27648step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw27648step1 raw27648step0; decide +kernel
      have hl : raw27648step1Labels = raw27648step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27648step0 raw27648step0Labels permutation32 permutation6
    mixedMoment B raw27648step1 raw27648step1Labels = mixedMoment B raw27648step2 raw27648step2Labels := by
      have ha : raw27648step2 = raw27648step1 := by apply Matrix.ext; unfold raw27648step2 raw27648step1; decide +kernel
      have hl : raw27648step1Labels = labelEmbedding9 ∘ raw27648step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27648step1 raw27648step1Labels raw27648step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4807 node4807Labels := by rfl

def raw27649 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw27649Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27649step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw27649step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27649step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27649step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw27649step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27649step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27649 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27649 raw27649Labels = mixedMoment B node5078 node5078Labels := by
  calc
    mixedMoment B raw27649 raw27649Labels = mixedMoment B raw27649step0 raw27649step0Labels := by
      have hz : ∀ j, raw27649 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27649step0 = (fun i j => raw27649 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27649step0 raw27649; decide +kernel
      have hl : raw27649step0Labels = raw27649Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27649 raw27649Labels permutation434 hz
    mixedMoment B raw27649step0 raw27649step0Labels = mixedMoment B raw27649step1 raw27649step1Labels := by
      have ha : raw27649step1 = (fun i j => raw27649step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw27649step1 raw27649step0; decide +kernel
      have hl : raw27649step1Labels = raw27649step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27649step0 raw27649step0Labels permutation32 permutation6
    mixedMoment B raw27649step1 raw27649step1Labels = mixedMoment B raw27649step2 raw27649step2Labels := by
      have ha : raw27649step2 = raw27649step1 := by apply Matrix.ext; unfold raw27649step2 raw27649step1; decide +kernel
      have hl : raw27649step1Labels = labelEmbedding9 ∘ raw27649step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27649step1 raw27649step1Labels raw27649step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5078 node5078Labels := by rfl

def raw27650 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw27650Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27650step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27650step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw27650step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27650step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27650 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27650 raw27650Labels = mixedMoment B node5128 node5128Labels := by
  calc
    mixedMoment B raw27650 raw27650Labels = mixedMoment B raw27650step0 raw27650step0Labels := by
      have ha : raw27650step0 = (fun i j => raw27650 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw27650step0 raw27650; decide +kernel
      have hl : raw27650step0Labels = raw27650Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27650 raw27650Labels permutation158 permutation6
    mixedMoment B raw27650step0 raw27650step0Labels = mixedMoment B raw27650step1 raw27650step1Labels := by
      have ha : raw27650step1 = raw27650step0 := by apply Matrix.ext; unfold raw27650step1 raw27650step0; decide +kernel
      have hl : raw27650step0Labels = labelEmbedding9 ∘ raw27650step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27650step0 raw27650step0Labels raw27650step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5128 node5128Labels := by rfl

def raw27651 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw27651Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27651step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw27651step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27651step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw27651step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw27651step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27651step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw27651step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27651step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27651 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27651 raw27651Labels = mixedMoment B node5078 node5078Labels := by
  calc
    mixedMoment B raw27651 raw27651Labels = mixedMoment B raw27651step0 raw27651step0Labels := by
      have hz : ∀ j, raw27651 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27651step0 = (fun i j => raw27651 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27651step0 raw27651; decide +kernel
      have hl : raw27651step0Labels = raw27651Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27651 raw27651Labels permutation434 hz
    mixedMoment B raw27651step0 raw27651step0Labels = mixedMoment B raw27651step1 raw27651step1Labels := by
      have ha : raw27651step1 = (fun i j => raw27651step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27651step1 raw27651step0; decide +kernel
      have hl : raw27651step1Labels = raw27651step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27651step0 raw27651step0Labels permutation151 permutation7
    mixedMoment B raw27651step1 raw27651step1Labels = mixedMoment B raw27651step2 raw27651step2Labels := by
      have ha : raw27651step2 = -raw27651step1 := by apply Matrix.ext; change ∀ i j, raw27651step2 i j = -(raw27651step1 i j); unfold raw27651step2 raw27651step1; decide +kernel
      have hl : raw27651step2Labels = raw27651step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27651step2 raw27651step2Labels = mixedMoment B raw27651step3 raw27651step3Labels := by
      have ha : raw27651step3 = raw27651step2 := by apply Matrix.ext; unfold raw27651step3 raw27651step2; decide +kernel
      have hl : raw27651step2Labels = labelEmbedding10 ∘ raw27651step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27651step2 raw27651step2Labels raw27651step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5078 node5078Labels := by rfl

def raw27652 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw27652Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27652step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw27652step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27652step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw27652step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw27652step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27652step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw27652step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27652step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27652 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27652 raw27652Labels = mixedMoment B node4807 node4807Labels := by
  calc
    mixedMoment B raw27652 raw27652Labels = mixedMoment B raw27652step0 raw27652step0Labels := by
      have hz : ∀ j, raw27652 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27652step0 = (fun i j => raw27652 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27652step0 raw27652; decide +kernel
      have hl : raw27652step0Labels = raw27652Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27652 raw27652Labels permutation434 hz
    mixedMoment B raw27652step0 raw27652step0Labels = mixedMoment B raw27652step1 raw27652step1Labels := by
      have ha : raw27652step1 = (fun i j => raw27652step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27652step1 raw27652step0; decide +kernel
      have hl : raw27652step1Labels = raw27652step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27652step0 raw27652step0Labels permutation151 permutation7
    mixedMoment B raw27652step1 raw27652step1Labels = mixedMoment B raw27652step2 raw27652step2Labels := by
      have ha : raw27652step2 = -raw27652step1 := by apply Matrix.ext; change ∀ i j, raw27652step2 i j = -(raw27652step1 i j); unfold raw27652step2 raw27652step1; decide +kernel
      have hl : raw27652step2Labels = raw27652step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27652step2 raw27652step2Labels = mixedMoment B raw27652step3 raw27652step3Labels := by
      have ha : raw27652step3 = raw27652step2 := by apply Matrix.ext; unfold raw27652step3 raw27652step2; decide +kernel
      have hl : raw27652step2Labels = labelEmbedding10 ∘ raw27652step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27652step2 raw27652step2Labels raw27652step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4807 node4807Labels := by rfl

def raw27653 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw27653Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27653step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw27653step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27653step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27653step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw27653step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27653step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27653 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27653 raw27653Labels = mixedMoment B node4807 node4807Labels := by
  calc
    mixedMoment B raw27653 raw27653Labels = mixedMoment B raw27653step0 raw27653step0Labels := by
      have hz : ∀ j, raw27653 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27653step0 = (fun i j => raw27653 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27653step0 raw27653; decide +kernel
      have hl : raw27653step0Labels = raw27653Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27653 raw27653Labels permutation346 hz
    mixedMoment B raw27653step0 raw27653step0Labels = mixedMoment B raw27653step1 raw27653step1Labels := by
      have ha : raw27653step1 = (fun i j => raw27653step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw27653step1 raw27653step0; decide +kernel
      have hl : raw27653step1Labels = raw27653step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27653step0 raw27653step0Labels permutation32 permutation6
    mixedMoment B raw27653step1 raw27653step1Labels = mixedMoment B raw27653step2 raw27653step2Labels := by
      have ha : raw27653step2 = raw27653step1 := by apply Matrix.ext; unfold raw27653step2 raw27653step1; decide +kernel
      have hl : raw27653step1Labels = labelEmbedding9 ∘ raw27653step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27653step1 raw27653step1Labels raw27653step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4807 node4807Labels := by rfl

def raw27654 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw27654Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27654step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw27654step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27654step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27654step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw27654step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27654step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27654 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27654 raw27654Labels = mixedMoment B node5078 node5078Labels := by
  calc
    mixedMoment B raw27654 raw27654Labels = mixedMoment B raw27654step0 raw27654step0Labels := by
      have hz : ∀ j, raw27654 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27654step0 = (fun i j => raw27654 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27654step0 raw27654; decide +kernel
      have hl : raw27654step0Labels = raw27654Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27654 raw27654Labels permutation346 hz
    mixedMoment B raw27654step0 raw27654step0Labels = mixedMoment B raw27654step1 raw27654step1Labels := by
      have ha : raw27654step1 = (fun i j => raw27654step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw27654step1 raw27654step0; decide +kernel
      have hl : raw27654step1Labels = raw27654step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27654step0 raw27654step0Labels permutation32 permutation6
    mixedMoment B raw27654step1 raw27654step1Labels = mixedMoment B raw27654step2 raw27654step2Labels := by
      have ha : raw27654step2 = raw27654step1 := by apply Matrix.ext; unfold raw27654step2 raw27654step1; decide +kernel
      have hl : raw27654step1Labels = labelEmbedding9 ∘ raw27654step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27654step1 raw27654step1Labels raw27654step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5078 node5078Labels := by rfl

def raw27655 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw27655Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27655step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27655step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw27655step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27655step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27655 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27655 raw27655Labels = mixedMoment B node5128 node5128Labels := by
  calc
    mixedMoment B raw27655 raw27655Labels = mixedMoment B raw27655step0 raw27655step0Labels := by
      have ha : raw27655step0 = (fun i j => raw27655 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw27655step0 raw27655; decide +kernel
      have hl : raw27655step0Labels = raw27655Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27655 raw27655Labels permutation152 permutation6
    mixedMoment B raw27655step0 raw27655step0Labels = mixedMoment B raw27655step1 raw27655step1Labels := by
      have ha : raw27655step1 = raw27655step0 := by apply Matrix.ext; unfold raw27655step1 raw27655step0; decide +kernel
      have hl : raw27655step0Labels = labelEmbedding9 ∘ raw27655step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27655step0 raw27655step0Labels raw27655step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5128 node5128Labels := by rfl

def raw27656 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw27656Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27656step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw27656step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27656step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw27656step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw27656step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27656step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw27656step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27656step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27656 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27656 raw27656Labels = mixedMoment B node5078 node5078Labels := by
  calc
    mixedMoment B raw27656 raw27656Labels = mixedMoment B raw27656step0 raw27656step0Labels := by
      have hz : ∀ j, raw27656 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27656step0 = (fun i j => raw27656 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27656step0 raw27656; decide +kernel
      have hl : raw27656step0Labels = raw27656Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27656 raw27656Labels permutation346 hz
    mixedMoment B raw27656step0 raw27656step0Labels = mixedMoment B raw27656step1 raw27656step1Labels := by
      have ha : raw27656step1 = (fun i j => raw27656step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27656step1 raw27656step0; decide +kernel
      have hl : raw27656step1Labels = raw27656step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27656step0 raw27656step0Labels permutation151 permutation7
    mixedMoment B raw27656step1 raw27656step1Labels = mixedMoment B raw27656step2 raw27656step2Labels := by
      have ha : raw27656step2 = -raw27656step1 := by apply Matrix.ext; change ∀ i j, raw27656step2 i j = -(raw27656step1 i j); unfold raw27656step2 raw27656step1; decide +kernel
      have hl : raw27656step2Labels = raw27656step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27656step2 raw27656step2Labels = mixedMoment B raw27656step3 raw27656step3Labels := by
      have ha : raw27656step3 = raw27656step2 := by apply Matrix.ext; unfold raw27656step3 raw27656step2; decide +kernel
      have hl : raw27656step2Labels = labelEmbedding10 ∘ raw27656step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27656step2 raw27656step2Labels raw27656step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5078 node5078Labels := by rfl

def raw27657 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw27657Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27657step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw27657step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27657step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw27657step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw27657step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27657step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw27657step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27657step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27657 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27657 raw27657Labels = mixedMoment B node4807 node4807Labels := by
  calc
    mixedMoment B raw27657 raw27657Labels = mixedMoment B raw27657step0 raw27657step0Labels := by
      have hz : ∀ j, raw27657 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27657step0 = (fun i j => raw27657 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27657step0 raw27657; decide +kernel
      have hl : raw27657step0Labels = raw27657Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27657 raw27657Labels permutation346 hz
    mixedMoment B raw27657step0 raw27657step0Labels = mixedMoment B raw27657step1 raw27657step1Labels := by
      have ha : raw27657step1 = (fun i j => raw27657step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27657step1 raw27657step0; decide +kernel
      have hl : raw27657step1Labels = raw27657step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27657step0 raw27657step0Labels permutation151 permutation7
    mixedMoment B raw27657step1 raw27657step1Labels = mixedMoment B raw27657step2 raw27657step2Labels := by
      have ha : raw27657step2 = -raw27657step1 := by apply Matrix.ext; change ∀ i j, raw27657step2 i j = -(raw27657step1 i j); unfold raw27657step2 raw27657step1; decide +kernel
      have hl : raw27657step2Labels = raw27657step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27657step2 raw27657step2Labels = mixedMoment B raw27657step3 raw27657step3Labels := by
      have ha : raw27657step3 = raw27657step2 := by apply Matrix.ext; unfold raw27657step3 raw27657step2; decide +kernel
      have hl : raw27657step2Labels = labelEmbedding10 ∘ raw27657step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27657step2 raw27657step2Labels raw27657step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4807 node4807Labels := by rfl

def raw27658 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw27658Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27658step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw27658step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27658step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -2, 1], ![-2, -1, 3]]
def raw27658step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27658step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw27658step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw27658step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw27658step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27658 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27658 raw27658Labels = mixedMoment B node4843 node4843Labels := by
  calc
    mixedMoment B raw27658 raw27658Labels = mixedMoment B raw27658step0 raw27658step0Labels := by
      have hz : ∀ j, raw27658 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27658step0 = (fun i j => raw27658 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27658step0 raw27658; decide +kernel
      have hl : raw27658step0Labels = raw27658Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27658 raw27658Labels permutation434 hz
    mixedMoment B raw27658step0 raw27658step0Labels = mixedMoment B raw27658step1 raw27658step1Labels := by
      have hz : ∀ j, raw27658step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27658step1 = (fun i j => raw27658step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27658step1 raw27658step0; decide +kernel
      have hl : raw27658step1Labels = raw27658step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27658step0 raw27658step0Labels permutation80 hz
    mixedMoment B raw27658step1 raw27658step1Labels = mixedMoment B raw27658step2 raw27658step2Labels := by
      have ha : raw27658step2 = (fun i j => raw27658step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw27658step2 raw27658step1; decide +kernel
      have hl : raw27658step2Labels = raw27658step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27658step1 raw27658step1Labels permutation8 permutation6
    mixedMoment B raw27658step2 raw27658step2Labels = mixedMoment B raw27658step3 raw27658step3Labels := by
      have ha : raw27658step3 = raw27658step2 := by apply Matrix.ext; unfold raw27658step3 raw27658step2; decide +kernel
      have hl : raw27658step2Labels = labelEmbedding9 ∘ raw27658step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27658step2 raw27658step2Labels raw27658step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4843 node4843Labels := by rfl

def raw27659 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw27659Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27659step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw27659step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27659step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -2, 1], ![-2, -1, 3]]
def raw27659step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27659step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw27659step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw27659step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw27659step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27659 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27659 raw27659Labels = mixedMoment B node5109 node5109Labels := by
  calc
    mixedMoment B raw27659 raw27659Labels = mixedMoment B raw27659step0 raw27659step0Labels := by
      have hz : ∀ j, raw27659 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27659step0 = (fun i j => raw27659 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27659step0 raw27659; decide +kernel
      have hl : raw27659step0Labels = raw27659Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27659 raw27659Labels permutation434 hz
    mixedMoment B raw27659step0 raw27659step0Labels = mixedMoment B raw27659step1 raw27659step1Labels := by
      have hz : ∀ j, raw27659step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27659step1 = (fun i j => raw27659step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27659step1 raw27659step0; decide +kernel
      have hl : raw27659step1Labels = raw27659step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27659step0 raw27659step0Labels permutation80 hz
    mixedMoment B raw27659step1 raw27659step1Labels = mixedMoment B raw27659step2 raw27659step2Labels := by
      have ha : raw27659step2 = (fun i j => raw27659step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw27659step2 raw27659step1; decide +kernel
      have hl : raw27659step2Labels = raw27659step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27659step1 raw27659step1Labels permutation8 permutation6
    mixedMoment B raw27659step2 raw27659step2Labels = mixedMoment B raw27659step3 raw27659step3Labels := by
      have ha : raw27659step3 = raw27659step2 := by apply Matrix.ext; unfold raw27659step3 raw27659step2; decide +kernel
      have hl : raw27659step2Labels = labelEmbedding9 ∘ raw27659step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27659step2 raw27659step2Labels raw27659step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5109 node5109Labels := by rfl

def raw27660 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw27660Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27660step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw27660step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27660step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw27660step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw27660step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw27660step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27660 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27660 raw27660Labels = mixedMoment B node5139 node5139Labels := by
  calc
    mixedMoment B raw27660 raw27660Labels = mixedMoment B raw27660step0 raw27660step0Labels := by
      have hz : ∀ j, raw27660 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27660step0 = (fun i j => raw27660 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27660step0 raw27660; decide +kernel
      have hl : raw27660step0Labels = raw27660Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27660 raw27660Labels permutation434 hz
    mixedMoment B raw27660step0 raw27660step0Labels = mixedMoment B raw27660step1 raw27660step1Labels := by
      have ha : raw27660step1 = (fun i j => raw27660step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw27660step1 raw27660step0; decide +kernel
      have hl : raw27660step1Labels = raw27660step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27660step0 raw27660step0Labels permutation32 permutation6
    mixedMoment B raw27660step1 raw27660step1Labels = mixedMoment B raw27660step2 raw27660step2Labels := by
      have ha : raw27660step2 = raw27660step1 := by apply Matrix.ext; unfold raw27660step2 raw27660step1; decide +kernel
      have hl : raw27660step1Labels = labelEmbedding9 ∘ raw27660step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27660step1 raw27660step1Labels raw27660step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5139 node5139Labels := by rfl

def raw27661 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw27661Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27661step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw27661step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27661step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw27661step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw27661step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw27661step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27661 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27661 raw27661Labels = mixedMoment B node5139 node5139Labels := by
  calc
    mixedMoment B raw27661 raw27661Labels = mixedMoment B raw27661step0 raw27661step0Labels := by
      have hz : ∀ j, raw27661 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27661step0 = (fun i j => raw27661 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27661step0 raw27661; decide +kernel
      have hl : raw27661step0Labels = raw27661Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27661 raw27661Labels permutation346 hz
    mixedMoment B raw27661step0 raw27661step0Labels = mixedMoment B raw27661step1 raw27661step1Labels := by
      have ha : raw27661step1 = (fun i j => raw27661step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw27661step1 raw27661step0; decide +kernel
      have hl : raw27661step1Labels = raw27661step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27661step0 raw27661step0Labels permutation32 permutation6
    mixedMoment B raw27661step1 raw27661step1Labels = mixedMoment B raw27661step2 raw27661step2Labels := by
      have ha : raw27661step2 = raw27661step1 := by apply Matrix.ext; unfold raw27661step2 raw27661step1; decide +kernel
      have hl : raw27661step1Labels = labelEmbedding9 ∘ raw27661step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27661step1 raw27661step1Labels raw27661step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5139 node5139Labels := by rfl

def raw27662 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw27662Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27662step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw27662step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27662step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -2, 1], ![-3, 0, 3]]
def raw27662step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27662step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw27662step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw27662step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27662step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw27662step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27662step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27662 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27662 raw27662Labels = mixedMoment B node4871 node4871Labels := by
  calc
    mixedMoment B raw27662 raw27662Labels = mixedMoment B raw27662step0 raw27662step0Labels := by
      have hz : ∀ j, raw27662 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27662step0 = (fun i j => raw27662 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27662step0 raw27662; decide +kernel
      have hl : raw27662step0Labels = raw27662Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27662 raw27662Labels permutation434 hz
    mixedMoment B raw27662step0 raw27662step0Labels = mixedMoment B raw27662step1 raw27662step1Labels := by
      have hz : ∀ j, raw27662step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27662step1 = (fun i j => raw27662step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27662step1 raw27662step0; decide +kernel
      have hl : raw27662step1Labels = raw27662step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27662step0 raw27662step0Labels permutation80 hz
    mixedMoment B raw27662step1 raw27662step1Labels = mixedMoment B raw27662step2 raw27662step2Labels := by
      have ha : raw27662step2 = (fun i j => raw27662step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27662step2 raw27662step1; decide +kernel
      have hl : raw27662step2Labels = raw27662step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27662step1 raw27662step1Labels permutation31 permutation7
    mixedMoment B raw27662step2 raw27662step2Labels = mixedMoment B raw27662step3 raw27662step3Labels := by
      have ha : raw27662step3 = -raw27662step2 := by apply Matrix.ext; change ∀ i j, raw27662step3 i j = -(raw27662step2 i j); unfold raw27662step3 raw27662step2; decide +kernel
      have hl : raw27662step3Labels = raw27662step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27662step3 raw27662step3Labels = mixedMoment B raw27662step4 raw27662step4Labels := by
      have ha : raw27662step4 = raw27662step3 := by apply Matrix.ext; unfold raw27662step4 raw27662step3; decide +kernel
      have hl : raw27662step3Labels = labelEmbedding10 ∘ raw27662step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27662step3 raw27662step3Labels raw27662step4Labels labelEmbedding10 hl
    _ = mixedMoment B node4871 node4871Labels := by rfl

def raw27663 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw27663Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27663step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw27663step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27663step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, -1, 1], ![-1, -2, 3]]
def raw27663step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27663step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw27663step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw27663step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw27663step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27663 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27663 raw27663Labels = mixedMoment B node4841 node4841Labels := by
  calc
    mixedMoment B raw27663 raw27663Labels = mixedMoment B raw27663step0 raw27663step0Labels := by
      have hz : ∀ j, raw27663 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27663step0 = (fun i j => raw27663 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27663step0 raw27663; decide +kernel
      have hl : raw27663step0Labels = raw27663Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27663 raw27663Labels permutation434 hz
    mixedMoment B raw27663step0 raw27663step0Labels = mixedMoment B raw27663step1 raw27663step1Labels := by
      have hz : ∀ j, raw27663step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27663step1 = (fun i j => raw27663step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27663step1 raw27663step0; decide +kernel
      have hl : raw27663step1Labels = raw27663step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27663step0 raw27663step0Labels permutation80 hz
    mixedMoment B raw27663step1 raw27663step1Labels = mixedMoment B raw27663step2 raw27663step2Labels := by
      have ha : raw27663step2 = (fun i j => raw27663step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw27663step2 raw27663step1; decide +kernel
      have hl : raw27663step2Labels = raw27663step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27663step1 raw27663step1Labels permutation8 permutation6
    mixedMoment B raw27663step2 raw27663step2Labels = mixedMoment B raw27663step3 raw27663step3Labels := by
      have ha : raw27663step3 = raw27663step2 := by apply Matrix.ext; unfold raw27663step3 raw27663step2; decide +kernel
      have hl : raw27663step2Labels = labelEmbedding9 ∘ raw27663step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27663step2 raw27663step2Labels raw27663step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4841 node4841Labels := by rfl

def raw27664 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw27664Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27664step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw27664step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27664step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, -1, 1], ![-1, -2, 3]]
def raw27664step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27664step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw27664step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw27664step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw27664step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27664 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27664 raw27664Labels = mixedMoment B node5107 node5107Labels := by
  calc
    mixedMoment B raw27664 raw27664Labels = mixedMoment B raw27664step0 raw27664step0Labels := by
      have hz : ∀ j, raw27664 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27664step0 = (fun i j => raw27664 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27664step0 raw27664; decide +kernel
      have hl : raw27664step0Labels = raw27664Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27664 raw27664Labels permutation434 hz
    mixedMoment B raw27664step0 raw27664step0Labels = mixedMoment B raw27664step1 raw27664step1Labels := by
      have hz : ∀ j, raw27664step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27664step1 = (fun i j => raw27664step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27664step1 raw27664step0; decide +kernel
      have hl : raw27664step1Labels = raw27664step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27664step0 raw27664step0Labels permutation80 hz
    mixedMoment B raw27664step1 raw27664step1Labels = mixedMoment B raw27664step2 raw27664step2Labels := by
      have ha : raw27664step2 = (fun i j => raw27664step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw27664step2 raw27664step1; decide +kernel
      have hl : raw27664step2Labels = raw27664step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27664step1 raw27664step1Labels permutation8 permutation6
    mixedMoment B raw27664step2 raw27664step2Labels = mixedMoment B raw27664step3 raw27664step3Labels := by
      have ha : raw27664step3 = raw27664step2 := by apply Matrix.ext; unfold raw27664step3 raw27664step2; decide +kernel
      have hl : raw27664step2Labels = labelEmbedding9 ∘ raw27664step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27664step2 raw27664step2Labels raw27664step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5107 node5107Labels := by rfl

def raw27665 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw27665Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27665step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw27665step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27665step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw27665step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw27665step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw27665step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw27665step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw27665step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27665 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27665 raw27665Labels = mixedMoment B node5075 node5075Labels := by
  calc
    mixedMoment B raw27665 raw27665Labels = mixedMoment B raw27665step0 raw27665step0Labels := by
      have hz : ∀ j, raw27665 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27665step0 = (fun i j => raw27665 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27665step0 raw27665; decide +kernel
      have hl : raw27665step0Labels = raw27665Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27665 raw27665Labels permutation434 hz
    mixedMoment B raw27665step0 raw27665step0Labels = mixedMoment B raw27665step1 raw27665step1Labels := by
      have ha : raw27665step1 = (fun i j => raw27665step0 (permutation151 i) (permutation6 j)) := by apply Matrix.ext; unfold raw27665step1 raw27665step0; decide +kernel
      have hl : raw27665step1Labels = raw27665step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27665step0 raw27665step0Labels permutation151 permutation6
    mixedMoment B raw27665step1 raw27665step1Labels = mixedMoment B raw27665step2 raw27665step2Labels := by
      have ha : raw27665step2 = -raw27665step1 := by apply Matrix.ext; change ∀ i j, raw27665step2 i j = -(raw27665step1 i j); unfold raw27665step2 raw27665step1; decide +kernel
      have hl : raw27665step2Labels = raw27665step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27665step2 raw27665step2Labels = mixedMoment B raw27665step3 raw27665step3Labels := by
      have ha : raw27665step3 = raw27665step2 := by apply Matrix.ext; unfold raw27665step3 raw27665step2; decide +kernel
      have hl : raw27665step2Labels = labelEmbedding9 ∘ raw27665step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27665step2 raw27665step2Labels raw27665step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5075 node5075Labels := by rfl

def raw27666 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw27666Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27666step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw27666step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27666step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw27666step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw27666step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw27666step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw27666step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw27666step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27666 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27666 raw27666Labels = mixedMoment B node5075 node5075Labels := by
  calc
    mixedMoment B raw27666 raw27666Labels = mixedMoment B raw27666step0 raw27666step0Labels := by
      have hz : ∀ j, raw27666 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27666step0 = (fun i j => raw27666 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27666step0 raw27666; decide +kernel
      have hl : raw27666step0Labels = raw27666Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27666 raw27666Labels permutation346 hz
    mixedMoment B raw27666step0 raw27666step0Labels = mixedMoment B raw27666step1 raw27666step1Labels := by
      have ha : raw27666step1 = (fun i j => raw27666step0 (permutation151 i) (permutation6 j)) := by apply Matrix.ext; unfold raw27666step1 raw27666step0; decide +kernel
      have hl : raw27666step1Labels = raw27666step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27666step0 raw27666step0Labels permutation151 permutation6
    mixedMoment B raw27666step1 raw27666step1Labels = mixedMoment B raw27666step2 raw27666step2Labels := by
      have ha : raw27666step2 = -raw27666step1 := by apply Matrix.ext; change ∀ i j, raw27666step2 i j = -(raw27666step1 i j); unfold raw27666step2 raw27666step1; decide +kernel
      have hl : raw27666step2Labels = raw27666step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27666step2 raw27666step2Labels = mixedMoment B raw27666step3 raw27666step3Labels := by
      have ha : raw27666step3 = raw27666step2 := by apply Matrix.ext; unfold raw27666step3 raw27666step2; decide +kernel
      have hl : raw27666step2Labels = labelEmbedding9 ∘ raw27666step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27666step2 raw27666step2Labels raw27666step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5075 node5075Labels := by rfl

def raw27667 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw27667Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27667step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw27667step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27667step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 0, 1], ![-1, -2, 3]]
def raw27667step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27667step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw27667step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw27667step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw27667step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27667 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27667 raw27667Labels = mixedMoment B node5171 node5171Labels := by
  calc
    mixedMoment B raw27667 raw27667Labels = mixedMoment B raw27667step0 raw27667step0Labels := by
      have hz : ∀ j, raw27667 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27667step0 = (fun i j => raw27667 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27667step0 raw27667; decide +kernel
      have hl : raw27667step0Labels = raw27667Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27667 raw27667Labels permutation434 hz
    mixedMoment B raw27667step0 raw27667step0Labels = mixedMoment B raw27667step1 raw27667step1Labels := by
      have hz : ∀ j, raw27667step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27667step1 = (fun i j => raw27667step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27667step1 raw27667step0; decide +kernel
      have hl : raw27667step1Labels = raw27667step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27667step0 raw27667step0Labels permutation80 hz
    mixedMoment B raw27667step1 raw27667step1Labels = mixedMoment B raw27667step2 raw27667step2Labels := by
      have ha : raw27667step2 = (fun i j => raw27667step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw27667step2 raw27667step1; decide +kernel
      have hl : raw27667step2Labels = raw27667step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27667step1 raw27667step1Labels permutation8 permutation6
    mixedMoment B raw27667step2 raw27667step2Labels = mixedMoment B raw27667step3 raw27667step3Labels := by
      have ha : raw27667step3 = raw27667step2 := by apply Matrix.ext; unfold raw27667step3 raw27667step2; decide +kernel
      have hl : raw27667step2Labels = labelEmbedding9 ∘ raw27667step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27667step2 raw27667step2Labels raw27667step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5171 node5171Labels := by rfl

def raw27668 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw27668Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27668step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw27668step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27668step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![1, -2, 1], ![-2, 0, 2], ![-3, 2, 1]]
def raw27668step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27668step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![2, 0, -2], ![3, -2, -1]]
def raw27668step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27668step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![2, 0, -2], ![3, -2, -1]]
def raw27668step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27668 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27668 raw27668Labels = mixedMoment B node4727 node4727Labels := by
  calc
    mixedMoment B raw27668 raw27668Labels = mixedMoment B raw27668step0 raw27668step0Labels := by
      have hz : ∀ j, raw27668 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27668step0 = (fun i j => raw27668 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27668step0 raw27668; decide +kernel
      have hl : raw27668step0Labels = raw27668Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27668 raw27668Labels permutation434 hz
    mixedMoment B raw27668step0 raw27668step0Labels = mixedMoment B raw27668step1 raw27668step1Labels := by
      have ha : raw27668step1 = (fun i j => raw27668step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27668step1 raw27668step0; decide +kernel
      have hl : raw27668step1Labels = raw27668step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27668step0 raw27668step0Labels permutation145 permutation3
    mixedMoment B raw27668step1 raw27668step1Labels = mixedMoment B raw27668step2 raw27668step2Labels := by
      have ha : raw27668step2 = -raw27668step1 := by apply Matrix.ext; change ∀ i j, raw27668step2 i j = -(raw27668step1 i j); unfold raw27668step2 raw27668step1; decide +kernel
      have hl : raw27668step2Labels = raw27668step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27668step2 raw27668step2Labels = mixedMoment B raw27668step3 raw27668step3Labels := by
      have ha : raw27668step3 = raw27668step2 := by apply Matrix.ext; unfold raw27668step3 raw27668step2; decide +kernel
      have hl : raw27668step2Labels = labelEmbedding6 ∘ raw27668step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27668step2 raw27668step2Labels raw27668step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4727 node4727Labels := by rfl

def raw27669 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![-1, 1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw27669Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27669step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw27669step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27669step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27669step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27669step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27669step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27669 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27669 raw27669Labels = mixedMoment B node4723 node4723Labels := by
  calc
    mixedMoment B raw27669 raw27669Labels = mixedMoment B raw27669step0 raw27669step0Labels := by
      have ha : raw27669step0 = (fun i j => raw27669 (permutation644 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27669step0 raw27669; decide +kernel
      have hl : raw27669step0Labels = raw27669Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27669 raw27669Labels permutation644 permutation3
    mixedMoment B raw27669step0 raw27669step0Labels = mixedMoment B raw27669step1 raw27669step1Labels := by
      have ha : raw27669step1 = -raw27669step0 := by apply Matrix.ext; change ∀ i j, raw27669step1 i j = -(raw27669step0 i j); unfold raw27669step1 raw27669step0; decide +kernel
      have hl : raw27669step1Labels = raw27669step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27669step1 raw27669step1Labels = mixedMoment B raw27669step2 raw27669step2Labels := by
      have ha : raw27669step2 = raw27669step1 := by apply Matrix.ext; unfold raw27669step2 raw27669step1; decide +kernel
      have hl : raw27669step1Labels = labelEmbedding6 ∘ raw27669step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27669step1 raw27669step1Labels raw27669step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4723 node4723Labels := by rfl

def raw27670 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw27670Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27670step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw27670step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27670step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![1, -2, 1], ![-2, 0, 2], ![-3, 2, 1]]
def raw27670step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27670step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![2, 0, -2], ![3, -2, -1]]
def raw27670step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27670step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![2, 0, -2], ![3, -2, -1]]
def raw27670step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27670 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27670 raw27670Labels = mixedMoment B node4727 node4727Labels := by
  calc
    mixedMoment B raw27670 raw27670Labels = mixedMoment B raw27670step0 raw27670step0Labels := by
      have hz : ∀ j, raw27670 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27670step0 = (fun i j => raw27670 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27670step0 raw27670; decide +kernel
      have hl : raw27670step0Labels = raw27670Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27670 raw27670Labels permutation346 hz
    mixedMoment B raw27670step0 raw27670step0Labels = mixedMoment B raw27670step1 raw27670step1Labels := by
      have ha : raw27670step1 = (fun i j => raw27670step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27670step1 raw27670step0; decide +kernel
      have hl : raw27670step1Labels = raw27670step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27670step0 raw27670step0Labels permutation145 permutation3
    mixedMoment B raw27670step1 raw27670step1Labels = mixedMoment B raw27670step2 raw27670step2Labels := by
      have ha : raw27670step2 = -raw27670step1 := by apply Matrix.ext; change ∀ i j, raw27670step2 i j = -(raw27670step1 i j); unfold raw27670step2 raw27670step1; decide +kernel
      have hl : raw27670step2Labels = raw27670step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27670step2 raw27670step2Labels = mixedMoment B raw27670step3 raw27670step3Labels := by
      have ha : raw27670step3 = raw27670step2 := by apply Matrix.ext; unfold raw27670step3 raw27670step2; decide +kernel
      have hl : raw27670step2Labels = labelEmbedding6 ∘ raw27670step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27670step2 raw27670step2Labels raw27670step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4727 node4727Labels := by rfl

def raw27671 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw27671Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27671step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw27671step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27671step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27671step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27671step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27671step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27671 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27671 raw27671Labels = mixedMoment B node4723 node4723Labels := by
  calc
    mixedMoment B raw27671 raw27671Labels = mixedMoment B raw27671step0 raw27671step0Labels := by
      have ha : raw27671step0 = (fun i j => raw27671 (permutation662 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27671step0 raw27671; decide +kernel
      have hl : raw27671step0Labels = raw27671Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27671 raw27671Labels permutation662 permutation3
    mixedMoment B raw27671step0 raw27671step0Labels = mixedMoment B raw27671step1 raw27671step1Labels := by
      have ha : raw27671step1 = -raw27671step0 := by apply Matrix.ext; change ∀ i j, raw27671step1 i j = -(raw27671step0 i j); unfold raw27671step1 raw27671step0; decide +kernel
      have hl : raw27671step1Labels = raw27671step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27671step1 raw27671step1Labels = mixedMoment B raw27671step2 raw27671step2Labels := by
      have ha : raw27671step2 = raw27671step1 := by apply Matrix.ext; unfold raw27671step2 raw27671step1; decide +kernel
      have hl : raw27671step1Labels = labelEmbedding6 ∘ raw27671step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27671step1 raw27671step1Labels raw27671step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4723 node4723Labels := by rfl

def raw27672 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw27672Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27672step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw27672step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27672step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![2, 0, -2], ![3, -3, 0]]
def raw27672step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27672step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-2, 0, 2], ![-3, 2, 1]]
def raw27672step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27672step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, 0, -2], ![3, -2, -1]]
def raw27672step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27672step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, 0, -2], ![3, -2, -1]]
def raw27672step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27672 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27672 raw27672Labels = mixedMoment B node4693 node4693Labels := by
  calc
    mixedMoment B raw27672 raw27672Labels = mixedMoment B raw27672step0 raw27672step0Labels := by
      have hz : ∀ j, raw27672 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27672step0 = (fun i j => raw27672 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27672step0 raw27672; decide +kernel
      have hl : raw27672step0Labels = raw27672Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27672 raw27672Labels permutation434 hz
    mixedMoment B raw27672step0 raw27672step0Labels = mixedMoment B raw27672step1 raw27672step1Labels := by
      have hz : ∀ j, raw27672step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27672step1 = (fun i j => raw27672step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27672step1 raw27672step0; decide +kernel
      have hl : raw27672step1Labels = raw27672step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27672step0 raw27672step0Labels permutation80 hz
    mixedMoment B raw27672step1 raw27672step1Labels = mixedMoment B raw27672step2 raw27672step2Labels := by
      have ha : raw27672step2 = (fun i j => raw27672step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27672step2 raw27672step1; decide +kernel
      have hl : raw27672step2Labels = raw27672step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27672step1 raw27672step1Labels permutation31 permutation3
    mixedMoment B raw27672step2 raw27672step2Labels = mixedMoment B raw27672step3 raw27672step3Labels := by
      have ha : raw27672step3 = -raw27672step2 := by apply Matrix.ext; change ∀ i j, raw27672step3 i j = -(raw27672step2 i j); unfold raw27672step3 raw27672step2; decide +kernel
      have hl : raw27672step3Labels = raw27672step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27672step3 raw27672step3Labels = mixedMoment B raw27672step4 raw27672step4Labels := by
      have ha : raw27672step4 = raw27672step3 := by apply Matrix.ext; unfold raw27672step4 raw27672step3; decide +kernel
      have hl : raw27672step3Labels = labelEmbedding6 ∘ raw27672step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27672step3 raw27672step3Labels raw27672step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4693 node4693Labels := by rfl

def raw27673 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw27673Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27673step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -3, 0]]
def raw27673step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27673step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw27673step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27673step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27673step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27673step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27673step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27673 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27673 raw27673Labels = mixedMoment B node4686 node4686Labels := by
  calc
    mixedMoment B raw27673 raw27673Labels = mixedMoment B raw27673step0 raw27673step0Labels := by
      have hz : ∀ j, raw27673 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27673step0 = (fun i j => raw27673 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27673step0 raw27673; decide +kernel
      have hl : raw27673step0Labels = raw27673Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27673 raw27673Labels permutation434 hz
    mixedMoment B raw27673step0 raw27673step0Labels = mixedMoment B raw27673step1 raw27673step1Labels := by
      have ha : raw27673step1 = (fun i j => raw27673step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27673step1 raw27673step0; decide +kernel
      have hl : raw27673step1Labels = raw27673step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27673step0 raw27673step0Labels permutation149 permutation3
    mixedMoment B raw27673step1 raw27673step1Labels = mixedMoment B raw27673step2 raw27673step2Labels := by
      have ha : raw27673step2 = -raw27673step1 := by apply Matrix.ext; change ∀ i j, raw27673step2 i j = -(raw27673step1 i j); unfold raw27673step2 raw27673step1; decide +kernel
      have hl : raw27673step2Labels = raw27673step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27673step2 raw27673step2Labels = mixedMoment B raw27673step3 raw27673step3Labels := by
      have ha : raw27673step3 = raw27673step2 := by apply Matrix.ext; unfold raw27673step3 raw27673step2; decide +kernel
      have hl : raw27673step2Labels = labelEmbedding6 ∘ raw27673step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27673step2 raw27673step2Labels raw27673step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4686 node4686Labels := by rfl

def raw27674 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -3, 0]]
def raw27674Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27674step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -3, 0]]
def raw27674step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27674step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw27674step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27674step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27674step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27674step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27674step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27674 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27674 raw27674Labels = mixedMoment B node4686 node4686Labels := by
  calc
    mixedMoment B raw27674 raw27674Labels = mixedMoment B raw27674step0 raw27674step0Labels := by
      have hz : ∀ j, raw27674 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27674step0 = (fun i j => raw27674 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27674step0 raw27674; decide +kernel
      have hl : raw27674step0Labels = raw27674Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27674 raw27674Labels permutation346 hz
    mixedMoment B raw27674step0 raw27674step0Labels = mixedMoment B raw27674step1 raw27674step1Labels := by
      have ha : raw27674step1 = (fun i j => raw27674step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27674step1 raw27674step0; decide +kernel
      have hl : raw27674step1Labels = raw27674step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27674step0 raw27674step0Labels permutation149 permutation3
    mixedMoment B raw27674step1 raw27674step1Labels = mixedMoment B raw27674step2 raw27674step2Labels := by
      have ha : raw27674step2 = -raw27674step1 := by apply Matrix.ext; change ∀ i j, raw27674step2 i j = -(raw27674step1 i j); unfold raw27674step2 raw27674step1; decide +kernel
      have hl : raw27674step2Labels = raw27674step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27674step2 raw27674step2Labels = mixedMoment B raw27674step3 raw27674step3Labels := by
      have ha : raw27674step3 = raw27674step2 := by apply Matrix.ext; unfold raw27674step3 raw27674step2; decide +kernel
      have hl : raw27674step2Labels = labelEmbedding6 ∘ raw27674step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27674step2 raw27674step2Labels raw27674step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4686 node4686Labels := by rfl

def raw27675 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![4, -4, 0]]
def raw27675Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27675step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![1, 1, -2], ![4, -4, 0]]
def raw27675step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27675step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 1, -2], ![4, -4, 0]]
def raw27675step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27675step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![1, -2, 1], ![-2, 0, 2], ![-3, 2, 1]]
def raw27675step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27675step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![2, 0, -2], ![3, -2, -1]]
def raw27675step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27675step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![2, 0, -2], ![3, -2, -1]]
def raw27675step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27675 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27675 raw27675Labels = mixedMoment B node4243 node4243Labels := by
  calc
    mixedMoment B raw27675 raw27675Labels = mixedMoment B raw27675step0 raw27675step0Labels := by
      have hz : ∀ j, raw27675 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27675step0 = (fun i j => raw27675 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27675step0 raw27675; decide +kernel
      have hl : raw27675step0Labels = raw27675Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27675 raw27675Labels permutation434 hz
    mixedMoment B raw27675step0 raw27675step0Labels = mixedMoment B raw27675step1 raw27675step1Labels := by
      have hz : ∀ j, raw27675step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27675step1 = (fun i j => raw27675step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27675step1 raw27675step0; decide +kernel
      have hl : raw27675step1Labels = raw27675step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27675step0 raw27675step0Labels permutation80 hz
    mixedMoment B raw27675step1 raw27675step1Labels = mixedMoment B raw27675step2 raw27675step2Labels := by
      have ha : raw27675step2 = (fun i j => raw27675step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27675step2 raw27675step1; decide +kernel
      have hl : raw27675step2Labels = raw27675step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27675step1 raw27675step1Labels permutation31 permutation3
    mixedMoment B raw27675step2 raw27675step2Labels = mixedMoment B raw27675step3 raw27675step3Labels := by
      have ha : raw27675step3 = -raw27675step2 := by apply Matrix.ext; change ∀ i j, raw27675step3 i j = -(raw27675step2 i j); unfold raw27675step3 raw27675step2; decide +kernel
      have hl : raw27675step3Labels = raw27675step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27675step3 raw27675step3Labels = mixedMoment B raw27675step4 raw27675step4Labels := by
      have ha : raw27675step4 = raw27675step3 := by apply Matrix.ext; unfold raw27675step4 raw27675step3; decide +kernel
      have hl : raw27675step3Labels = labelEmbedding6 ∘ raw27675step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27675step3 raw27675step3Labels raw27675step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4243 node4243Labels := by rfl

def raw27676 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![4, -4, 0]]
def raw27676Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27676step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 1, -2], ![4, -4, 0]]
def raw27676step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27676step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw27676step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27676step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27676step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27676step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27676step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27676 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27676 raw27676Labels = mixedMoment B node4237 node4237Labels := by
  calc
    mixedMoment B raw27676 raw27676Labels = mixedMoment B raw27676step0 raw27676step0Labels := by
      have hz : ∀ j, raw27676 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27676step0 = (fun i j => raw27676 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27676step0 raw27676; decide +kernel
      have hl : raw27676step0Labels = raw27676Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27676 raw27676Labels permutation434 hz
    mixedMoment B raw27676step0 raw27676step0Labels = mixedMoment B raw27676step1 raw27676step1Labels := by
      have ha : raw27676step1 = (fun i j => raw27676step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27676step1 raw27676step0; decide +kernel
      have hl : raw27676step1Labels = raw27676step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27676step0 raw27676step0Labels permutation149 permutation3
    mixedMoment B raw27676step1 raw27676step1Labels = mixedMoment B raw27676step2 raw27676step2Labels := by
      have ha : raw27676step2 = -raw27676step1 := by apply Matrix.ext; change ∀ i j, raw27676step2 i j = -(raw27676step1 i j); unfold raw27676step2 raw27676step1; decide +kernel
      have hl : raw27676step2Labels = raw27676step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27676step2 raw27676step2Labels = mixedMoment B raw27676step3 raw27676step3Labels := by
      have ha : raw27676step3 = raw27676step2 := by apply Matrix.ext; unfold raw27676step3 raw27676step2; decide +kernel
      have hl : raw27676step2Labels = labelEmbedding6 ∘ raw27676step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27676step2 raw27676step2Labels raw27676step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4237 node4237Labels := by rfl

def raw27677 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![4, -4, 0]]
def raw27677Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27677step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 1, -2], ![4, -4, 0]]
def raw27677step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27677step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw27677step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27677step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27677step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27677step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27677step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27677 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27677 raw27677Labels = mixedMoment B node4237 node4237Labels := by
  calc
    mixedMoment B raw27677 raw27677Labels = mixedMoment B raw27677step0 raw27677step0Labels := by
      have hz : ∀ j, raw27677 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27677step0 = (fun i j => raw27677 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27677step0 raw27677; decide +kernel
      have hl : raw27677step0Labels = raw27677Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27677 raw27677Labels permutation346 hz
    mixedMoment B raw27677step0 raw27677step0Labels = mixedMoment B raw27677step1 raw27677step1Labels := by
      have ha : raw27677step1 = (fun i j => raw27677step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27677step1 raw27677step0; decide +kernel
      have hl : raw27677step1Labels = raw27677step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27677step0 raw27677step0Labels permutation149 permutation3
    mixedMoment B raw27677step1 raw27677step1Labels = mixedMoment B raw27677step2 raw27677step2Labels := by
      have ha : raw27677step2 = -raw27677step1 := by apply Matrix.ext; change ∀ i j, raw27677step2 i j = -(raw27677step1 i j); unfold raw27677step2 raw27677step1; decide +kernel
      have hl : raw27677step2Labels = raw27677step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27677step2 raw27677step2Labels = mixedMoment B raw27677step3 raw27677step3Labels := by
      have ha : raw27677step3 = raw27677step2 := by apply Matrix.ext; unfold raw27677step3 raw27677step2; decide +kernel
      have hl : raw27677step2Labels = labelEmbedding6 ∘ raw27677step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27677step2 raw27677step2Labels raw27677step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4237 node4237Labels := by rfl

def raw27678 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw27678Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27678step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw27678step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27678step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![1, -2, 1], ![-2, 0, 2], ![-3, 2, 1]]
def raw27678step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27678step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![2, 0, -2], ![3, -2, -1]]
def raw27678step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27678 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27678 raw27678Labels = mixedMoment B node1881 node1881Labels := by
  calc
    mixedMoment B raw27678 raw27678Labels = mixedMoment B raw27678step0 raw27678step0Labels := by
      have hz : ∀ j, raw27678 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27678step0 = (fun i j => raw27678 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27678step0 raw27678; decide +kernel
      have hl : raw27678step0Labels = raw27678Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27678 raw27678Labels permutation434 hz
    mixedMoment B raw27678step0 raw27678step0Labels = mixedMoment B raw27678step1 raw27678step1Labels := by
      have ha : raw27678step1 = (fun i j => raw27678step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27678step1 raw27678step0; decide +kernel
      have hl : raw27678step1Labels = raw27678step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27678step0 raw27678step0Labels permutation145 permutation3
    mixedMoment B raw27678step1 raw27678step1Labels = mixedMoment B raw27678step2 raw27678step2Labels := by
      have ha : raw27678step2 = -raw27678step1 := by apply Matrix.ext; change ∀ i j, raw27678step2 i j = -(raw27678step1 i j); unfold raw27678step2 raw27678step1; decide +kernel
      have hl : raw27678step2Labels = raw27678step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1881 node1881Labels := by rfl

def raw27679 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![-1, 1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw27679Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27679step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw27679step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27679step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27679step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27679 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27679 raw27679Labels = mixedMoment B node1877 node1877Labels := by
  calc
    mixedMoment B raw27679 raw27679Labels = mixedMoment B raw27679step0 raw27679step0Labels := by
      have ha : raw27679step0 = (fun i j => raw27679 (permutation644 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27679step0 raw27679; decide +kernel
      have hl : raw27679step0Labels = raw27679Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27679 raw27679Labels permutation644 permutation3
    mixedMoment B raw27679step0 raw27679step0Labels = mixedMoment B raw27679step1 raw27679step1Labels := by
      have ha : raw27679step1 = -raw27679step0 := by apply Matrix.ext; change ∀ i j, raw27679step1 i j = -(raw27679step0 i j); unfold raw27679step1 raw27679step0; decide +kernel
      have hl : raw27679step1Labels = raw27679step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1877 node1877Labels := by rfl

def raw27680 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw27680Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27680step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw27680step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27680step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![1, -2, 1], ![-2, 0, 2], ![-3, 2, 1]]
def raw27680step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27680step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![2, 0, -2], ![3, -2, -1]]
def raw27680step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27680 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27680 raw27680Labels = mixedMoment B node1881 node1881Labels := by
  calc
    mixedMoment B raw27680 raw27680Labels = mixedMoment B raw27680step0 raw27680step0Labels := by
      have hz : ∀ j, raw27680 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27680step0 = (fun i j => raw27680 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27680step0 raw27680; decide +kernel
      have hl : raw27680step0Labels = raw27680Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27680 raw27680Labels permutation346 hz
    mixedMoment B raw27680step0 raw27680step0Labels = mixedMoment B raw27680step1 raw27680step1Labels := by
      have ha : raw27680step1 = (fun i j => raw27680step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27680step1 raw27680step0; decide +kernel
      have hl : raw27680step1Labels = raw27680step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27680step0 raw27680step0Labels permutation145 permutation3
    mixedMoment B raw27680step1 raw27680step1Labels = mixedMoment B raw27680step2 raw27680step2Labels := by
      have ha : raw27680step2 = -raw27680step1 := by apply Matrix.ext; change ∀ i j, raw27680step2 i j = -(raw27680step1 i j); unfold raw27680step2 raw27680step1; decide +kernel
      have hl : raw27680step2Labels = raw27680step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1881 node1881Labels := by rfl

def raw27681 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw27681Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27681step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw27681step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27681step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27681step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27681 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27681 raw27681Labels = mixedMoment B node1877 node1877Labels := by
  calc
    mixedMoment B raw27681 raw27681Labels = mixedMoment B raw27681step0 raw27681step0Labels := by
      have ha : raw27681step0 = (fun i j => raw27681 (permutation662 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27681step0 raw27681; decide +kernel
      have hl : raw27681step0Labels = raw27681Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27681 raw27681Labels permutation662 permutation3
    mixedMoment B raw27681step0 raw27681step0Labels = mixedMoment B raw27681step1 raw27681step1Labels := by
      have ha : raw27681step1 = -raw27681step0 := by apply Matrix.ext; change ∀ i j, raw27681step1 i j = -(raw27681step0 i j); unfold raw27681step1 raw27681step0; decide +kernel
      have hl : raw27681step1Labels = raw27681step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1877 node1877Labels := by rfl

def raw27682 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw27682Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27682step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw27682step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27682step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![2, 0, -2], ![3, -3, 0]]
def raw27682step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27682step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-2, 0, 2], ![-3, 2, 1]]
def raw27682step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27682step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, 0, -2], ![3, -2, -1]]
def raw27682step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27682 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27682 raw27682Labels = mixedMoment B node1819 node1819Labels := by
  calc
    mixedMoment B raw27682 raw27682Labels = mixedMoment B raw27682step0 raw27682step0Labels := by
      have hz : ∀ j, raw27682 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27682step0 = (fun i j => raw27682 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27682step0 raw27682; decide +kernel
      have hl : raw27682step0Labels = raw27682Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27682 raw27682Labels permutation434 hz
    mixedMoment B raw27682step0 raw27682step0Labels = mixedMoment B raw27682step1 raw27682step1Labels := by
      have hz : ∀ j, raw27682step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27682step1 = (fun i j => raw27682step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27682step1 raw27682step0; decide +kernel
      have hl : raw27682step1Labels = raw27682step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27682step0 raw27682step0Labels permutation80 hz
    mixedMoment B raw27682step1 raw27682step1Labels = mixedMoment B raw27682step2 raw27682step2Labels := by
      have ha : raw27682step2 = (fun i j => raw27682step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27682step2 raw27682step1; decide +kernel
      have hl : raw27682step2Labels = raw27682step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27682step1 raw27682step1Labels permutation31 permutation3
    mixedMoment B raw27682step2 raw27682step2Labels = mixedMoment B raw27682step3 raw27682step3Labels := by
      have ha : raw27682step3 = -raw27682step2 := by apply Matrix.ext; change ∀ i j, raw27682step3 i j = -(raw27682step2 i j); unfold raw27682step3 raw27682step2; decide +kernel
      have hl : raw27682step3Labels = raw27682step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1819 node1819Labels := by rfl

def raw27683 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw27683Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27683step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -3, 0]]
def raw27683step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27683step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw27683step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27683step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27683step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27683 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27683 raw27683Labels = mixedMoment B node1812 node1812Labels := by
  calc
    mixedMoment B raw27683 raw27683Labels = mixedMoment B raw27683step0 raw27683step0Labels := by
      have hz : ∀ j, raw27683 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27683step0 = (fun i j => raw27683 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27683step0 raw27683; decide +kernel
      have hl : raw27683step0Labels = raw27683Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27683 raw27683Labels permutation434 hz
    mixedMoment B raw27683step0 raw27683step0Labels = mixedMoment B raw27683step1 raw27683step1Labels := by
      have ha : raw27683step1 = (fun i j => raw27683step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27683step1 raw27683step0; decide +kernel
      have hl : raw27683step1Labels = raw27683step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27683step0 raw27683step0Labels permutation149 permutation3
    mixedMoment B raw27683step1 raw27683step1Labels = mixedMoment B raw27683step2 raw27683step2Labels := by
      have ha : raw27683step2 = -raw27683step1 := by apply Matrix.ext; change ∀ i j, raw27683step2 i j = -(raw27683step1 i j); unfold raw27683step2 raw27683step1; decide +kernel
      have hl : raw27683step2Labels = raw27683step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1812 node1812Labels := by rfl

def raw27684 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -3, 0]]
def raw27684Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27684step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -3, 0]]
def raw27684step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27684step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw27684step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27684step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27684step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27684 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27684 raw27684Labels = mixedMoment B node1812 node1812Labels := by
  calc
    mixedMoment B raw27684 raw27684Labels = mixedMoment B raw27684step0 raw27684step0Labels := by
      have hz : ∀ j, raw27684 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27684step0 = (fun i j => raw27684 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27684step0 raw27684; decide +kernel
      have hl : raw27684step0Labels = raw27684Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27684 raw27684Labels permutation346 hz
    mixedMoment B raw27684step0 raw27684step0Labels = mixedMoment B raw27684step1 raw27684step1Labels := by
      have ha : raw27684step1 = (fun i j => raw27684step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27684step1 raw27684step0; decide +kernel
      have hl : raw27684step1Labels = raw27684step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27684step0 raw27684step0Labels permutation149 permutation3
    mixedMoment B raw27684step1 raw27684step1Labels = mixedMoment B raw27684step2 raw27684step2Labels := by
      have ha : raw27684step2 = -raw27684step1 := by apply Matrix.ext; change ∀ i j, raw27684step2 i j = -(raw27684step1 i j); unfold raw27684step2 raw27684step1; decide +kernel
      have hl : raw27684step2Labels = raw27684step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1812 node1812Labels := by rfl

def raw27685 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![4, -4, 0]]
def raw27685Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27685step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![1, 1, -2], ![4, -4, 0]]
def raw27685step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27685step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 1, -2], ![4, -4, 0]]
def raw27685step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27685step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![1, -2, 1], ![-2, 0, 2], ![-3, 2, 1]]
def raw27685step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27685step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![2, 0, -2], ![3, -2, -1]]
def raw27685step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27685 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27685 raw27685Labels = mixedMoment B node743 node743Labels := by
  calc
    mixedMoment B raw27685 raw27685Labels = mixedMoment B raw27685step0 raw27685step0Labels := by
      have hz : ∀ j, raw27685 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27685step0 = (fun i j => raw27685 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27685step0 raw27685; decide +kernel
      have hl : raw27685step0Labels = raw27685Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27685 raw27685Labels permutation434 hz
    mixedMoment B raw27685step0 raw27685step0Labels = mixedMoment B raw27685step1 raw27685step1Labels := by
      have hz : ∀ j, raw27685step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27685step1 = (fun i j => raw27685step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27685step1 raw27685step0; decide +kernel
      have hl : raw27685step1Labels = raw27685step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27685step0 raw27685step0Labels permutation80 hz
    mixedMoment B raw27685step1 raw27685step1Labels = mixedMoment B raw27685step2 raw27685step2Labels := by
      have ha : raw27685step2 = (fun i j => raw27685step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27685step2 raw27685step1; decide +kernel
      have hl : raw27685step2Labels = raw27685step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27685step1 raw27685step1Labels permutation31 permutation3
    mixedMoment B raw27685step2 raw27685step2Labels = mixedMoment B raw27685step3 raw27685step3Labels := by
      have ha : raw27685step3 = -raw27685step2 := by apply Matrix.ext; change ∀ i j, raw27685step3 i j = -(raw27685step2 i j); unfold raw27685step3 raw27685step2; decide +kernel
      have hl : raw27685step3Labels = raw27685step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node743 node743Labels := by rfl

def raw27686 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![4, -4, 0]]
def raw27686Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27686step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 1, -2], ![4, -4, 0]]
def raw27686step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27686step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw27686step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27686step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27686step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27686 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27686 raw27686Labels = mixedMoment B node737 node737Labels := by
  calc
    mixedMoment B raw27686 raw27686Labels = mixedMoment B raw27686step0 raw27686step0Labels := by
      have hz : ∀ j, raw27686 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27686step0 = (fun i j => raw27686 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27686step0 raw27686; decide +kernel
      have hl : raw27686step0Labels = raw27686Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27686 raw27686Labels permutation434 hz
    mixedMoment B raw27686step0 raw27686step0Labels = mixedMoment B raw27686step1 raw27686step1Labels := by
      have ha : raw27686step1 = (fun i j => raw27686step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27686step1 raw27686step0; decide +kernel
      have hl : raw27686step1Labels = raw27686step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27686step0 raw27686step0Labels permutation149 permutation3
    mixedMoment B raw27686step1 raw27686step1Labels = mixedMoment B raw27686step2 raw27686step2Labels := by
      have ha : raw27686step2 = -raw27686step1 := by apply Matrix.ext; change ∀ i j, raw27686step2 i j = -(raw27686step1 i j); unfold raw27686step2 raw27686step1; decide +kernel
      have hl : raw27686step2Labels = raw27686step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node737 node737Labels := by rfl

def raw27687 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![4, -4, 0]]
def raw27687Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27687step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 1, -2], ![4, -4, 0]]
def raw27687step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27687step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw27687step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27687step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27687step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27687 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27687 raw27687Labels = mixedMoment B node737 node737Labels := by
  calc
    mixedMoment B raw27687 raw27687Labels = mixedMoment B raw27687step0 raw27687step0Labels := by
      have hz : ∀ j, raw27687 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27687step0 = (fun i j => raw27687 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27687step0 raw27687; decide +kernel
      have hl : raw27687step0Labels = raw27687Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27687 raw27687Labels permutation346 hz
    mixedMoment B raw27687step0 raw27687step0Labels = mixedMoment B raw27687step1 raw27687step1Labels := by
      have ha : raw27687step1 = (fun i j => raw27687step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27687step1 raw27687step0; decide +kernel
      have hl : raw27687step1Labels = raw27687step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27687step0 raw27687step0Labels permutation149 permutation3
    mixedMoment B raw27687step1 raw27687step1Labels = mixedMoment B raw27687step2 raw27687step2Labels := by
      have ha : raw27687step2 = -raw27687step1 := by apply Matrix.ext; change ∀ i j, raw27687step2 i j = -(raw27687step1 i j); unfold raw27687step2 raw27687step1; decide +kernel
      have hl : raw27687step2Labels = raw27687step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node737 node737Labels := by rfl

def raw27688 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw27688Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27688step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw27688step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27688step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -2, 1], ![3, 0, -3]]
def raw27688step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27688step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw27688step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27688step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw27688step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27688 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27688 raw27688Labels = mixedMoment B node4875 node4875Labels := by
  calc
    mixedMoment B raw27688 raw27688Labels = mixedMoment B raw27688step0 raw27688step0Labels := by
      have hz : ∀ j, raw27688 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27688step0 = (fun i j => raw27688 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27688step0 raw27688; decide +kernel
      have hl : raw27688step0Labels = raw27688Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27688 raw27688Labels permutation434 hz
    mixedMoment B raw27688step0 raw27688step0Labels = mixedMoment B raw27688step1 raw27688step1Labels := by
      have hz : ∀ j, raw27688step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27688step1 = (fun i j => raw27688step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27688step1 raw27688step0; decide +kernel
      have hl : raw27688step1Labels = raw27688step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27688step0 raw27688step0Labels permutation80 hz
    mixedMoment B raw27688step1 raw27688step1Labels = mixedMoment B raw27688step2 raw27688step2Labels := by
      have ha : raw27688step2 = (fun i j => raw27688step1 (permutation30 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27688step2 raw27688step1; decide +kernel
      have hl : raw27688step2Labels = raw27688step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27688step1 raw27688step1Labels permutation30 permutation2
    mixedMoment B raw27688step2 raw27688step2Labels = mixedMoment B raw27688step3 raw27688step3Labels := by
      have ha : raw27688step3 = -raw27688step2 := by apply Matrix.ext; change ∀ i j, raw27688step3 i j = -(raw27688step2 i j); unfold raw27688step3 raw27688step2; decide +kernel
      have hl : raw27688step3Labels = raw27688step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4875 node4875Labels := by rfl

def raw27689 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw27689Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27689step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw27689step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27689step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw27689step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27689step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw27689step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27689 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27689 raw27689Labels = mixedMoment B node4866 node4866Labels := by
  calc
    mixedMoment B raw27689 raw27689Labels = mixedMoment B raw27689step0 raw27689step0Labels := by
      have hz : ∀ j, raw27689 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27689step0 = (fun i j => raw27689 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27689step0 raw27689; decide +kernel
      have hl : raw27689step0Labels = raw27689Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27689 raw27689Labels permutation434 hz
    mixedMoment B raw27689step0 raw27689step0Labels = mixedMoment B raw27689step1 raw27689step1Labels := by
      have ha : raw27689step1 = (fun i j => raw27689step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27689step1 raw27689step0; decide +kernel
      have hl : raw27689step1Labels = raw27689step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27689step0 raw27689step0Labels permutation151 permutation2
    mixedMoment B raw27689step1 raw27689step1Labels = mixedMoment B raw27689step2 raw27689step2Labels := by
      have ha : raw27689step2 = -raw27689step1 := by apply Matrix.ext; change ∀ i j, raw27689step2 i j = -(raw27689step1 i j); unfold raw27689step2 raw27689step1; decide +kernel
      have hl : raw27689step2Labels = raw27689step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4866 node4866Labels := by rfl

def raw27690 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw27690Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27690step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw27690step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27690step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw27690step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27690step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw27690step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27690 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27690 raw27690Labels = mixedMoment B node4866 node4866Labels := by
  calc
    mixedMoment B raw27690 raw27690Labels = mixedMoment B raw27690step0 raw27690step0Labels := by
      have hz : ∀ j, raw27690 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27690step0 = (fun i j => raw27690 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27690step0 raw27690; decide +kernel
      have hl : raw27690step0Labels = raw27690Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27690 raw27690Labels permutation346 hz
    mixedMoment B raw27690step0 raw27690step0Labels = mixedMoment B raw27690step1 raw27690step1Labels := by
      have ha : raw27690step1 = (fun i j => raw27690step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27690step1 raw27690step0; decide +kernel
      have hl : raw27690step1Labels = raw27690step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27690step0 raw27690step0Labels permutation151 permutation2
    mixedMoment B raw27690step1 raw27690step1Labels = mixedMoment B raw27690step2 raw27690step2Labels := by
      have ha : raw27690step2 = -raw27690step1 := by apply Matrix.ext; change ∀ i j, raw27690step2 i j = -(raw27690step1 i j); unfold raw27690step2 raw27690step1; decide +kernel
      have hl : raw27690step2Labels = raw27690step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4866 node4866Labels := by rfl

def raw27691 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw27691Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27691step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw27691step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27691step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![3, 0, -3]]
def raw27691step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27691step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw27691step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27691step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw27691step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27691 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27691 raw27691Labels = mixedMoment B node4895 node4895Labels := by
  calc
    mixedMoment B raw27691 raw27691Labels = mixedMoment B raw27691step0 raw27691step0Labels := by
      have hz : ∀ j, raw27691 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27691step0 = (fun i j => raw27691 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27691step0 raw27691; decide +kernel
      have hl : raw27691step0Labels = raw27691Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27691 raw27691Labels permutation434 hz
    mixedMoment B raw27691step0 raw27691step0Labels = mixedMoment B raw27691step1 raw27691step1Labels := by
      have hz : ∀ j, raw27691step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27691step1 = (fun i j => raw27691step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27691step1 raw27691step0; decide +kernel
      have hl : raw27691step1Labels = raw27691step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27691step0 raw27691step0Labels permutation80 hz
    mixedMoment B raw27691step1 raw27691step1Labels = mixedMoment B raw27691step2 raw27691step2Labels := by
      have ha : raw27691step2 = (fun i j => raw27691step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27691step2 raw27691step1; decide +kernel
      have hl : raw27691step2Labels = raw27691step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27691step1 raw27691step1Labels permutation31 permutation2
    mixedMoment B raw27691step2 raw27691step2Labels = mixedMoment B raw27691step3 raw27691step3Labels := by
      have ha : raw27691step3 = -raw27691step2 := by apply Matrix.ext; change ∀ i j, raw27691step3 i j = -(raw27691step2 i j); unfold raw27691step3 raw27691step2; decide +kernel
      have hl : raw27691step3Labels = raw27691step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4895 node4895Labels := by rfl

def raw27692 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw27692Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27692step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw27692step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27692step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![2, 1, -3]]
def raw27692step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27692step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw27692step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw27692step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw27692step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27692 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27692 raw27692Labels = mixedMoment B node5304 node5304Labels := by
  calc
    mixedMoment B raw27692 raw27692Labels = mixedMoment B raw27692step0 raw27692step0Labels := by
      have hz : ∀ j, raw27692 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27692step0 = (fun i j => raw27692 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27692step0 raw27692; decide +kernel
      have hl : raw27692step0Labels = raw27692Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27692 raw27692Labels permutation434 hz
    mixedMoment B raw27692step0 raw27692step0Labels = mixedMoment B raw27692step1 raw27692step1Labels := by
      have hz : ∀ j, raw27692step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27692step1 = (fun i j => raw27692step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27692step1 raw27692step0; decide +kernel
      have hl : raw27692step1Labels = raw27692step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27692step0 raw27692step0Labels permutation80 hz
    mixedMoment B raw27692step1 raw27692step1Labels = mixedMoment B raw27692step2 raw27692step2Labels := by
      have ha : raw27692step2 = (fun i j => raw27692step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27692step2 raw27692step1; decide +kernel
      have hl : raw27692step2Labels = raw27692step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27692step1 raw27692step1Labels permutation31 permutation7
    mixedMoment B raw27692step2 raw27692step2Labels = mixedMoment B raw27692step3 raw27692step3Labels := by
      have ha : raw27692step3 = raw27692step2 := by apply Matrix.ext; unfold raw27692step3 raw27692step2; decide +kernel
      have hl : raw27692step2Labels = labelEmbedding10 ∘ raw27692step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27692step2 raw27692step2Labels raw27692step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5304 node5304Labels := by rfl

def raw27693 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw27693Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27693step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw27693step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27693step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -2, 1], ![3, 0, -3]]
def raw27693step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27693step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw27693step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27693step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw27693step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27693 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27693 raw27693Labels = mixedMoment B node4464 node4464Labels := by
  calc
    mixedMoment B raw27693 raw27693Labels = mixedMoment B raw27693step0 raw27693step0Labels := by
      have hz : ∀ j, raw27693 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27693step0 = (fun i j => raw27693 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27693step0 raw27693; decide +kernel
      have hl : raw27693step0Labels = raw27693Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27693 raw27693Labels permutation434 hz
    mixedMoment B raw27693step0 raw27693step0Labels = mixedMoment B raw27693step1 raw27693step1Labels := by
      have hz : ∀ j, raw27693step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27693step1 = (fun i j => raw27693step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27693step1 raw27693step0; decide +kernel
      have hl : raw27693step1Labels = raw27693step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27693step0 raw27693step0Labels permutation80 hz
    mixedMoment B raw27693step1 raw27693step1Labels = mixedMoment B raw27693step2 raw27693step2Labels := by
      have ha : raw27693step2 = (fun i j => raw27693step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27693step2 raw27693step1; decide +kernel
      have hl : raw27693step2Labels = raw27693step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27693step1 raw27693step1Labels permutation8 permutation3
    mixedMoment B raw27693step2 raw27693step2Labels = mixedMoment B raw27693step3 raw27693step3Labels := by
      have ha : raw27693step3 = raw27693step2 := by apply Matrix.ext; unfold raw27693step3 raw27693step2; decide +kernel
      have hl : raw27693step2Labels = labelEmbedding6 ∘ raw27693step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27693step2 raw27693step2Labels raw27693step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4464 node4464Labels := by rfl

def raw27694 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw27694Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27694step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw27694step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27694step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 2, 1]]
def raw27694step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27694step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw27694step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27694 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27694 raw27694Labels = mixedMoment B node4853 node4853Labels := by
  calc
    mixedMoment B raw27694 raw27694Labels = mixedMoment B raw27694step0 raw27694step0Labels := by
      have hz : ∀ j, raw27694 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27694step0 = (fun i j => raw27694 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27694step0 raw27694; decide +kernel
      have hl : raw27694step0Labels = raw27694Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27694 raw27694Labels permutation434 hz
    mixedMoment B raw27694step0 raw27694step0Labels = mixedMoment B raw27694step1 raw27694step1Labels := by
      have ha : raw27694step1 = (fun i j => raw27694step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27694step1 raw27694step0; decide +kernel
      have hl : raw27694step1Labels = raw27694step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27694step0 raw27694step0Labels permutation149 permutation2
    mixedMoment B raw27694step1 raw27694step1Labels = mixedMoment B raw27694step2 raw27694step2Labels := by
      have ha : raw27694step2 = -raw27694step1 := by apply Matrix.ext; change ∀ i j, raw27694step2 i j = -(raw27694step1 i j); unfold raw27694step2 raw27694step1; decide +kernel
      have hl : raw27694step2Labels = raw27694step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4853 node4853Labels := by rfl

def raw27695 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw27695Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27695step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw27695step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27695step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 2, 1]]
def raw27695step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27695step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw27695step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27695 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27695 raw27695Labels = mixedMoment B node4853 node4853Labels := by
  calc
    mixedMoment B raw27695 raw27695Labels = mixedMoment B raw27695step0 raw27695step0Labels := by
      have hz : ∀ j, raw27695 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27695step0 = (fun i j => raw27695 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27695step0 raw27695; decide +kernel
      have hl : raw27695step0Labels = raw27695Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27695 raw27695Labels permutation346 hz
    mixedMoment B raw27695step0 raw27695step0Labels = mixedMoment B raw27695step1 raw27695step1Labels := by
      have ha : raw27695step1 = (fun i j => raw27695step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27695step1 raw27695step0; decide +kernel
      have hl : raw27695step1Labels = raw27695step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27695step0 raw27695step0Labels permutation149 permutation2
    mixedMoment B raw27695step1 raw27695step1Labels = mixedMoment B raw27695step2 raw27695step2Labels := by
      have ha : raw27695step2 = -raw27695step1 := by apply Matrix.ext; change ∀ i j, raw27695step2 i j = -(raw27695step1 i j); unfold raw27695step2 raw27695step1; decide +kernel
      have hl : raw27695step2Labels = raw27695step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4853 node4853Labels := by rfl

def raw27696 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw27696Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27696step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw27696step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27696step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![3, 0, -3]]
def raw27696step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27696step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw27696step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27696step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw27696step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27696 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27696 raw27696Labels = mixedMoment B node4890 node4890Labels := by
  calc
    mixedMoment B raw27696 raw27696Labels = mixedMoment B raw27696step0 raw27696step0Labels := by
      have hz : ∀ j, raw27696 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27696step0 = (fun i j => raw27696 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27696step0 raw27696; decide +kernel
      have hl : raw27696step0Labels = raw27696Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27696 raw27696Labels permutation434 hz
    mixedMoment B raw27696step0 raw27696step0Labels = mixedMoment B raw27696step1 raw27696step1Labels := by
      have hz : ∀ j, raw27696step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27696step1 = (fun i j => raw27696step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27696step1 raw27696step0; decide +kernel
      have hl : raw27696step1Labels = raw27696step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27696step0 raw27696step0Labels permutation80 hz
    mixedMoment B raw27696step1 raw27696step1Labels = mixedMoment B raw27696step2 raw27696step2Labels := by
      have ha : raw27696step2 = (fun i j => raw27696step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27696step2 raw27696step1; decide +kernel
      have hl : raw27696step2Labels = raw27696step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27696step1 raw27696step1Labels permutation29 permutation2
    mixedMoment B raw27696step2 raw27696step2Labels = mixedMoment B raw27696step3 raw27696step3Labels := by
      have ha : raw27696step3 = -raw27696step2 := by apply Matrix.ext; change ∀ i j, raw27696step3 i j = -(raw27696step2 i j); unfold raw27696step3 raw27696step2; decide +kernel
      have hl : raw27696step3Labels = raw27696step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4890 node4890Labels := by rfl

def raw27697 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw27697Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27697step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw27697step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27697step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw27697step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27697step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw27697step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27697step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw27697step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27697 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27697 raw27697Labels = mixedMoment B node5295 node5295Labels := by
  calc
    mixedMoment B raw27697 raw27697Labels = mixedMoment B raw27697step0 raw27697step0Labels := by
      have hz : ∀ j, raw27697 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27697step0 = (fun i j => raw27697 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27697step0 raw27697; decide +kernel
      have hl : raw27697step0Labels = raw27697Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27697 raw27697Labels permutation434 hz
    mixedMoment B raw27697step0 raw27697step0Labels = mixedMoment B raw27697step1 raw27697step1Labels := by
      have hz : ∀ j, raw27697step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27697step1 = (fun i j => raw27697step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27697step1 raw27697step0; decide +kernel
      have hl : raw27697step1Labels = raw27697step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27697step0 raw27697step0Labels permutation80 hz
    mixedMoment B raw27697step1 raw27697step1Labels = mixedMoment B raw27697step2 raw27697step2Labels := by
      have ha : raw27697step2 = (fun i j => raw27697step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27697step2 raw27697step1; decide +kernel
      have hl : raw27697step2Labels = raw27697step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27697step1 raw27697step1Labels permutation8 permutation3
    mixedMoment B raw27697step2 raw27697step2Labels = mixedMoment B raw27697step3 raw27697step3Labels := by
      have ha : raw27697step3 = raw27697step2 := by apply Matrix.ext; unfold raw27697step3 raw27697step2; decide +kernel
      have hl : raw27697step2Labels = labelEmbedding6 ∘ raw27697step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27697step2 raw27697step2Labels raw27697step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5295 node5295Labels := by rfl

def raw27698 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw27698Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27698step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw27698step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27698step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw27698step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27698step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw27698step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27698 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27698 raw27698Labels = mixedMoment B node4353 node4353Labels := by
  calc
    mixedMoment B raw27698 raw27698Labels = mixedMoment B raw27698step0 raw27698step0Labels := by
      have hz : ∀ j, raw27698 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27698step0 = (fun i j => raw27698 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27698step0 raw27698; decide +kernel
      have hl : raw27698step0Labels = raw27698Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27698 raw27698Labels permutation434 hz
    mixedMoment B raw27698step0 raw27698step0Labels = mixedMoment B raw27698step1 raw27698step1Labels := by
      have ha : raw27698step1 = (fun i j => raw27698step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27698step1 raw27698step0; decide +kernel
      have hl : raw27698step1Labels = raw27698step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27698step0 raw27698step0Labels permutation32 permutation3
    mixedMoment B raw27698step1 raw27698step1Labels = mixedMoment B raw27698step2 raw27698step2Labels := by
      have ha : raw27698step2 = raw27698step1 := by apply Matrix.ext; unfold raw27698step2 raw27698step1; decide +kernel
      have hl : raw27698step1Labels = labelEmbedding6 ∘ raw27698step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27698step1 raw27698step1Labels raw27698step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4353 node4353Labels := by rfl

def raw27699 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw27699Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27699step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw27699step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27699step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -2, 1], ![-2, 1, 1], ![-3, 2, 1]]
def raw27699step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27699step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, -1, -1], ![3, -2, -1]]
def raw27699step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27699 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27699 raw27699Labels = mixedMoment B node4777 node4777Labels := by
  calc
    mixedMoment B raw27699 raw27699Labels = mixedMoment B raw27699step0 raw27699step0Labels := by
      have hz : ∀ j, raw27699 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27699step0 = (fun i j => raw27699 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27699step0 raw27699; decide +kernel
      have hl : raw27699step0Labels = raw27699Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27699 raw27699Labels permutation434 hz
    mixedMoment B raw27699step0 raw27699step0Labels = mixedMoment B raw27699step1 raw27699step1Labels := by
      have ha : raw27699step1 = (fun i j => raw27699step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27699step1 raw27699step0; decide +kernel
      have hl : raw27699step1Labels = raw27699step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27699step0 raw27699step0Labels permutation145 permutation2
    mixedMoment B raw27699step1 raw27699step1Labels = mixedMoment B raw27699step2 raw27699step2Labels := by
      have ha : raw27699step2 = -raw27699step1 := by apply Matrix.ext; change ∀ i j, raw27699step2 i j = -(raw27699step1 i j); unfold raw27699step2 raw27699step1; decide +kernel
      have hl : raw27699step2Labels = raw27699step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4777 node4777Labels := by rfl

def raw27700 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw27700Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27700step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 2, 1]]
def raw27700step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27700step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw27700step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27700 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27700 raw27700Labels = mixedMoment B node4772 node4772Labels := by
  calc
    mixedMoment B raw27700 raw27700Labels = mixedMoment B raw27700step0 raw27700step0Labels := by
      have ha : raw27700step0 = (fun i j => raw27700 (permutation646 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27700step0 raw27700; decide +kernel
      have hl : raw27700step0Labels = raw27700Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27700 raw27700Labels permutation646 permutation2
    mixedMoment B raw27700step0 raw27700step0Labels = mixedMoment B raw27700step1 raw27700step1Labels := by
      have ha : raw27700step1 = -raw27700step0 := by apply Matrix.ext; change ∀ i j, raw27700step1 i j = -(raw27700step0 i j); unfold raw27700step1 raw27700step0; decide +kernel
      have hl : raw27700step1Labels = raw27700step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4772 node4772Labels := by rfl

def raw27701 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw27701Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27701step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw27701step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27701step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw27701step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27701step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27701step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27701 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27701 raw27701Labels = mixedMoment B node4807 node4807Labels := by
  calc
    mixedMoment B raw27701 raw27701Labels = mixedMoment B raw27701step0 raw27701step0Labels := by
      have hz : ∀ j, raw27701 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27701step0 = (fun i j => raw27701 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27701step0 raw27701; decide +kernel
      have hl : raw27701step0Labels = raw27701Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27701 raw27701Labels permutation434 hz
    mixedMoment B raw27701step0 raw27701step0Labels = mixedMoment B raw27701step1 raw27701step1Labels := by
      have ha : raw27701step1 = (fun i j => raw27701step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27701step1 raw27701step0; decide +kernel
      have hl : raw27701step1Labels = raw27701step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27701step0 raw27701step0Labels permutation145 permutation2
    mixedMoment B raw27701step1 raw27701step1Labels = mixedMoment B raw27701step2 raw27701step2Labels := by
      have ha : raw27701step2 = -raw27701step1 := by apply Matrix.ext; change ∀ i j, raw27701step2 i j = -(raw27701step1 i j); unfold raw27701step2 raw27701step1; decide +kernel
      have hl : raw27701step2Labels = raw27701step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4807 node4807Labels := by rfl

def raw27702 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw27702Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27702step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw27702step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27702step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw27702step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27702step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw27702step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27702 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27702 raw27702Labels = mixedMoment B node5173 node5173Labels := by
  calc
    mixedMoment B raw27702 raw27702Labels = mixedMoment B raw27702step0 raw27702step0Labels := by
      have hz : ∀ j, raw27702 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27702step0 = (fun i j => raw27702 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27702step0 raw27702; decide +kernel
      have hl : raw27702step0Labels = raw27702Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27702 raw27702Labels permutation434 hz
    mixedMoment B raw27702step0 raw27702step0Labels = mixedMoment B raw27702step1 raw27702step1Labels := by
      have ha : raw27702step1 = (fun i j => raw27702step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27702step1 raw27702step0; decide +kernel
      have hl : raw27702step1Labels = raw27702step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27702step0 raw27702step0Labels permutation32 permutation3
    mixedMoment B raw27702step1 raw27702step1Labels = mixedMoment B raw27702step2 raw27702step2Labels := by
      have ha : raw27702step2 = raw27702step1 := by apply Matrix.ext; unfold raw27702step2 raw27702step1; decide +kernel
      have hl : raw27702step1Labels = labelEmbedding6 ∘ raw27702step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27702step1 raw27702step1Labels raw27702step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5173 node5173Labels := by rfl

def raw27703 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw27703Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27703step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw27703step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27703step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw27703step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27703step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw27703step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27703 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27703 raw27703Labels = mixedMoment B node4353 node4353Labels := by
  calc
    mixedMoment B raw27703 raw27703Labels = mixedMoment B raw27703step0 raw27703step0Labels := by
      have hz : ∀ j, raw27703 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27703step0 = (fun i j => raw27703 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27703step0 raw27703; decide +kernel
      have hl : raw27703step0Labels = raw27703Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27703 raw27703Labels permutation346 hz
    mixedMoment B raw27703step0 raw27703step0Labels = mixedMoment B raw27703step1 raw27703step1Labels := by
      have ha : raw27703step1 = (fun i j => raw27703step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27703step1 raw27703step0; decide +kernel
      have hl : raw27703step1Labels = raw27703step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27703step0 raw27703step0Labels permutation32 permutation3
    mixedMoment B raw27703step1 raw27703step1Labels = mixedMoment B raw27703step2 raw27703step2Labels := by
      have ha : raw27703step2 = raw27703step1 := by apply Matrix.ext; unfold raw27703step2 raw27703step1; decide +kernel
      have hl : raw27703step1Labels = labelEmbedding6 ∘ raw27703step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27703step1 raw27703step1Labels raw27703step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4353 node4353Labels := by rfl

def raw27704 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw27704Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27704step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw27704step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27704step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -2, 1], ![-2, 1, 1], ![-3, 2, 1]]
def raw27704step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27704step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, -1, -1], ![3, -2, -1]]
def raw27704step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27704 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27704 raw27704Labels = mixedMoment B node4777 node4777Labels := by
  calc
    mixedMoment B raw27704 raw27704Labels = mixedMoment B raw27704step0 raw27704step0Labels := by
      have hz : ∀ j, raw27704 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27704step0 = (fun i j => raw27704 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27704step0 raw27704; decide +kernel
      have hl : raw27704step0Labels = raw27704Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27704 raw27704Labels permutation346 hz
    mixedMoment B raw27704step0 raw27704step0Labels = mixedMoment B raw27704step1 raw27704step1Labels := by
      have ha : raw27704step1 = (fun i j => raw27704step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27704step1 raw27704step0; decide +kernel
      have hl : raw27704step1Labels = raw27704step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27704step0 raw27704step0Labels permutation145 permutation2
    mixedMoment B raw27704step1 raw27704step1Labels = mixedMoment B raw27704step2 raw27704step2Labels := by
      have ha : raw27704step2 = -raw27704step1 := by apply Matrix.ext; change ∀ i j, raw27704step2 i j = -(raw27704step1 i j); unfold raw27704step2 raw27704step1; decide +kernel
      have hl : raw27704step2Labels = raw27704step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4777 node4777Labels := by rfl

def raw27705 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw27705Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27705step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 2, 1]]
def raw27705step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27705step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw27705step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27705 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27705 raw27705Labels = mixedMoment B node4772 node4772Labels := by
  calc
    mixedMoment B raw27705 raw27705Labels = mixedMoment B raw27705step0 raw27705step0Labels := by
      have ha : raw27705step0 = (fun i j => raw27705 (permutation664 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27705step0 raw27705; decide +kernel
      have hl : raw27705step0Labels = raw27705Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27705 raw27705Labels permutation664 permutation2
    mixedMoment B raw27705step0 raw27705step0Labels = mixedMoment B raw27705step1 raw27705step1Labels := by
      have ha : raw27705step1 = -raw27705step0 := by apply Matrix.ext; change ∀ i j, raw27705step1 i j = -(raw27705step0 i j); unfold raw27705step1 raw27705step0; decide +kernel
      have hl : raw27705step1Labels = raw27705step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4772 node4772Labels := by rfl

def raw27706 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw27706Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27706step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw27706step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27706step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw27706step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27706step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27706step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27706 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27706 raw27706Labels = mixedMoment B node4807 node4807Labels := by
  calc
    mixedMoment B raw27706 raw27706Labels = mixedMoment B raw27706step0 raw27706step0Labels := by
      have hz : ∀ j, raw27706 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27706step0 = (fun i j => raw27706 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27706step0 raw27706; decide +kernel
      have hl : raw27706step0Labels = raw27706Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27706 raw27706Labels permutation346 hz
    mixedMoment B raw27706step0 raw27706step0Labels = mixedMoment B raw27706step1 raw27706step1Labels := by
      have ha : raw27706step1 = (fun i j => raw27706step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27706step1 raw27706step0; decide +kernel
      have hl : raw27706step1Labels = raw27706step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27706step0 raw27706step0Labels permutation145 permutation2
    mixedMoment B raw27706step1 raw27706step1Labels = mixedMoment B raw27706step2 raw27706step2Labels := by
      have ha : raw27706step2 = -raw27706step1 := by apply Matrix.ext; change ∀ i j, raw27706step2 i j = -(raw27706step1 i j); unfold raw27706step2 raw27706step1; decide +kernel
      have hl : raw27706step2Labels = raw27706step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4807 node4807Labels := by rfl

def raw27707 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw27707Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27707step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw27707step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27707step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw27707step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27707step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw27707step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27707 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27707 raw27707Labels = mixedMoment B node5173 node5173Labels := by
  calc
    mixedMoment B raw27707 raw27707Labels = mixedMoment B raw27707step0 raw27707step0Labels := by
      have hz : ∀ j, raw27707 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27707step0 = (fun i j => raw27707 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27707step0 raw27707; decide +kernel
      have hl : raw27707step0Labels = raw27707Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27707 raw27707Labels permutation346 hz
    mixedMoment B raw27707step0 raw27707step0Labels = mixedMoment B raw27707step1 raw27707step1Labels := by
      have ha : raw27707step1 = (fun i j => raw27707step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27707step1 raw27707step0; decide +kernel
      have hl : raw27707step1Labels = raw27707step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27707step0 raw27707step0Labels permutation32 permutation3
    mixedMoment B raw27707step1 raw27707step1Labels = mixedMoment B raw27707step2 raw27707step2Labels := by
      have ha : raw27707step2 = raw27707step1 := by apply Matrix.ext; unfold raw27707step2 raw27707step1; decide +kernel
      have hl : raw27707step1Labels = labelEmbedding6 ∘ raw27707step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27707step1 raw27707step1Labels raw27707step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5173 node5173Labels := by rfl

def raw27708 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![3, 0, -3]]
def raw27708Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27708step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![2, -3, 1], ![3, 0, -3]]
def raw27708step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27708step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![2, -3, 1], ![3, 0, -3]]
def raw27708step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27708step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, 1, -3], ![3, -3, 0]]
def raw27708step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27708step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, 1, -3], ![3, -3, 0]]
def raw27708step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27708 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27708 raw27708Labels = mixedMoment B node4362 node4362Labels := by
  calc
    mixedMoment B raw27708 raw27708Labels = mixedMoment B raw27708step0 raw27708step0Labels := by
      have hz : ∀ j, raw27708 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27708step0 = (fun i j => raw27708 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27708step0 raw27708; decide +kernel
      have hl : raw27708step0Labels = raw27708Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27708 raw27708Labels permutation434 hz
    mixedMoment B raw27708step0 raw27708step0Labels = mixedMoment B raw27708step1 raw27708step1Labels := by
      have hz : ∀ j, raw27708step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27708step1 = (fun i j => raw27708step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27708step1 raw27708step0; decide +kernel
      have hl : raw27708step1Labels = raw27708step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27708step0 raw27708step0Labels permutation80 hz
    mixedMoment B raw27708step1 raw27708step1Labels = mixedMoment B raw27708step2 raw27708step2Labels := by
      have ha : raw27708step2 = (fun i j => raw27708step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27708step2 raw27708step1; decide +kernel
      have hl : raw27708step2Labels = raw27708step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27708step1 raw27708step1Labels permutation8 permutation3
    mixedMoment B raw27708step2 raw27708step2Labels = mixedMoment B raw27708step3 raw27708step3Labels := by
      have ha : raw27708step3 = raw27708step2 := by apply Matrix.ext; unfold raw27708step3 raw27708step2; decide +kernel
      have hl : raw27708step2Labels = labelEmbedding6 ∘ raw27708step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27708step2 raw27708step2Labels raw27708step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4362 node4362Labels := by rfl

def raw27709 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![3, 0, -3]]
def raw27709Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27709step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![2, -3, 1], ![3, 0, -3]]
def raw27709step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27709step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![2, -3, 1], ![3, 0, -3]]
def raw27709step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27709step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![2, -3, 1], ![-2, 1, 1], ![-3, 2, 1]]
def raw27709step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27709step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![2, -1, -1], ![3, -2, -1]]
def raw27709step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27709 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27709 raw27709Labels = mixedMoment B node4705 node4705Labels := by
  calc
    mixedMoment B raw27709 raw27709Labels = mixedMoment B raw27709step0 raw27709step0Labels := by
      have hz : ∀ j, raw27709 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27709step0 = (fun i j => raw27709 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27709step0 raw27709; decide +kernel
      have hl : raw27709step0Labels = raw27709Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27709 raw27709Labels permutation434 hz
    mixedMoment B raw27709step0 raw27709step0Labels = mixedMoment B raw27709step1 raw27709step1Labels := by
      have hz : ∀ j, raw27709step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27709step1 = (fun i j => raw27709step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27709step1 raw27709step0; decide +kernel
      have hl : raw27709step1Labels = raw27709step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27709step0 raw27709step0Labels permutation80 hz
    mixedMoment B raw27709step1 raw27709step1Labels = mixedMoment B raw27709step2 raw27709step2Labels := by
      have ha : raw27709step2 = (fun i j => raw27709step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27709step2 raw27709step1; decide +kernel
      have hl : raw27709step2Labels = raw27709step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27709step1 raw27709step1Labels permutation31 permutation2
    mixedMoment B raw27709step2 raw27709step2Labels = mixedMoment B raw27709step3 raw27709step3Labels := by
      have ha : raw27709step3 = -raw27709step2 := by apply Matrix.ext; change ∀ i j, raw27709step3 i j = -(raw27709step2 i j); unfold raw27709step3 raw27709step2; decide +kernel
      have hl : raw27709step3Labels = raw27709step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4705 node4705Labels := by rfl

def raw27710 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![3, 0, -3]]
def raw27710Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27710step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![2, -3, 1], ![3, 0, -3]]
def raw27710step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27710step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -3, 1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 2, 1]]
def raw27710step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27710step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw27710step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27710 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27710 raw27710Labels = mixedMoment B node4699 node4699Labels := by
  calc
    mixedMoment B raw27710 raw27710Labels = mixedMoment B raw27710step0 raw27710step0Labels := by
      have hz : ∀ j, raw27710 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27710step0 = (fun i j => raw27710 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27710step0 raw27710; decide +kernel
      have hl : raw27710step0Labels = raw27710Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27710 raw27710Labels permutation434 hz
    mixedMoment B raw27710step0 raw27710step0Labels = mixedMoment B raw27710step1 raw27710step1Labels := by
      have ha : raw27710step1 = (fun i j => raw27710step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27710step1 raw27710step0; decide +kernel
      have hl : raw27710step1Labels = raw27710step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27710step0 raw27710step0Labels permutation151 permutation2
    mixedMoment B raw27710step1 raw27710step1Labels = mixedMoment B raw27710step2 raw27710step2Labels := by
      have ha : raw27710step2 = -raw27710step1 := by apply Matrix.ext; change ∀ i j, raw27710step2 i j = -(raw27710step1 i j); unfold raw27710step2 raw27710step1; decide +kernel
      have hl : raw27710step2Labels = raw27710step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4699 node4699Labels := by rfl

def raw27711 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![3, 0, -3]]
def raw27711Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27711step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![2, -3, 1], ![3, 0, -3]]
def raw27711step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27711step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -3, 1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 2, 1]]
def raw27711step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27711step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw27711step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27711 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27711 raw27711Labels = mixedMoment B node4699 node4699Labels := by
  calc
    mixedMoment B raw27711 raw27711Labels = mixedMoment B raw27711step0 raw27711step0Labels := by
      have hz : ∀ j, raw27711 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27711step0 = (fun i j => raw27711 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27711step0 raw27711; decide +kernel
      have hl : raw27711step0Labels = raw27711Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27711 raw27711Labels permutation346 hz
    mixedMoment B raw27711step0 raw27711step0Labels = mixedMoment B raw27711step1 raw27711step1Labels := by
      have ha : raw27711step1 = (fun i j => raw27711step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27711step1 raw27711step0; decide +kernel
      have hl : raw27711step1Labels = raw27711step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27711step0 raw27711step0Labels permutation151 permutation2
    mixedMoment B raw27711step1 raw27711step1Labels = mixedMoment B raw27711step2 raw27711step2Labels := by
      have ha : raw27711step2 = -raw27711step1 := by apply Matrix.ext; change ∀ i j, raw27711step2 i j = -(raw27711step1 i j); unfold raw27711step2 raw27711step1; decide +kernel
      have hl : raw27711step2Labels = raw27711step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4699 node4699Labels := by rfl

def raw27712 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![2, 1, -3]]
def raw27712Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27712step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![2, -3, 1], ![2, 1, -3]]
def raw27712step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27712step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -3, 1], ![2, 1, -3]]
def raw27712step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27712step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -3, 1], ![2, 1, -3]]
def raw27712step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27712step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -3, 1], ![2, 1, -3]]
def raw27712step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27712 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27712 raw27712Labels = mixedMoment B node5175 node5175Labels := by
  calc
    mixedMoment B raw27712 raw27712Labels = mixedMoment B raw27712step0 raw27712step0Labels := by
      have hz : ∀ j, raw27712 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27712step0 = (fun i j => raw27712 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27712step0 raw27712; decide +kernel
      have hl : raw27712step0Labels = raw27712Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27712 raw27712Labels permutation434 hz
    mixedMoment B raw27712step0 raw27712step0Labels = mixedMoment B raw27712step1 raw27712step1Labels := by
      have hz : ∀ j, raw27712step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27712step1 = (fun i j => raw27712step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27712step1 raw27712step0; decide +kernel
      have hl : raw27712step1Labels = raw27712step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27712step0 raw27712step0Labels permutation80 hz
    mixedMoment B raw27712step1 raw27712step1Labels = mixedMoment B raw27712step2 raw27712step2Labels := by
      have ha : raw27712step2 = (fun i j => raw27712step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27712step2 raw27712step1; decide +kernel
      have hl : raw27712step2Labels = raw27712step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27712step1 raw27712step1Labels permutation9 permutation3
    mixedMoment B raw27712step2 raw27712step2Labels = mixedMoment B raw27712step3 raw27712step3Labels := by
      have ha : raw27712step3 = raw27712step2 := by apply Matrix.ext; unfold raw27712step3 raw27712step2; decide +kernel
      have hl : raw27712step2Labels = labelEmbedding6 ∘ raw27712step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27712step2 raw27712step2Labels raw27712step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5175 node5175Labels := by rfl

def raw27713 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![4, -1, -3]]
def raw27713Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27713step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![4, -1, -3]]
def raw27713step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27713step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -2, 1], ![4, -1, -3]]
def raw27713step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27713step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 1, -2], ![4, -3, -1]]
def raw27713step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27713step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 1, -2], ![4, -3, -1]]
def raw27713step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27713 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27713 raw27713Labels = mixedMoment B node4358 node4358Labels := by
  calc
    mixedMoment B raw27713 raw27713Labels = mixedMoment B raw27713step0 raw27713step0Labels := by
      have hz : ∀ j, raw27713 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27713step0 = (fun i j => raw27713 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27713step0 raw27713; decide +kernel
      have hl : raw27713step0Labels = raw27713Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27713 raw27713Labels permutation434 hz
    mixedMoment B raw27713step0 raw27713step0Labels = mixedMoment B raw27713step1 raw27713step1Labels := by
      have hz : ∀ j, raw27713step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27713step1 = (fun i j => raw27713step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27713step1 raw27713step0; decide +kernel
      have hl : raw27713step1Labels = raw27713step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27713step0 raw27713step0Labels permutation80 hz
    mixedMoment B raw27713step1 raw27713step1Labels = mixedMoment B raw27713step2 raw27713step2Labels := by
      have ha : raw27713step2 = (fun i j => raw27713step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27713step2 raw27713step1; decide +kernel
      have hl : raw27713step2Labels = raw27713step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27713step1 raw27713step1Labels permutation8 permutation3
    mixedMoment B raw27713step2 raw27713step2Labels = mixedMoment B raw27713step3 raw27713step3Labels := by
      have ha : raw27713step3 = raw27713step2 := by apply Matrix.ext; unfold raw27713step3 raw27713step2; decide +kernel
      have hl : raw27713step2Labels = labelEmbedding6 ∘ raw27713step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27713step2 raw27713step2Labels raw27713step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4358 node4358Labels := by rfl

def raw27714 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![4, -1, -3]]
def raw27714Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27714step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![1, -2, 1], ![4, -1, -3]]
def raw27714step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27714step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -2, 1], ![4, -1, -3]]
def raw27714step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27714step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![1, -2, 1], ![-2, 1, 1], ![-3, 2, 1]]
def raw27714step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27714step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![2, -1, -1], ![3, -2, -1]]
def raw27714step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27714 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27714 raw27714Labels = mixedMoment B node4374 node4374Labels := by
  calc
    mixedMoment B raw27714 raw27714Labels = mixedMoment B raw27714step0 raw27714step0Labels := by
      have hz : ∀ j, raw27714 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27714step0 = (fun i j => raw27714 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27714step0 raw27714; decide +kernel
      have hl : raw27714step0Labels = raw27714Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27714 raw27714Labels permutation434 hz
    mixedMoment B raw27714step0 raw27714step0Labels = mixedMoment B raw27714step1 raw27714step1Labels := by
      have hz : ∀ j, raw27714step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27714step1 = (fun i j => raw27714step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27714step1 raw27714step0; decide +kernel
      have hl : raw27714step1Labels = raw27714step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27714step0 raw27714step0Labels permutation80 hz
    mixedMoment B raw27714step1 raw27714step1Labels = mixedMoment B raw27714step2 raw27714step2Labels := by
      have ha : raw27714step2 = (fun i j => raw27714step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27714step2 raw27714step1; decide +kernel
      have hl : raw27714step2Labels = raw27714step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27714step1 raw27714step1Labels permutation31 permutation2
    mixedMoment B raw27714step2 raw27714step2Labels = mixedMoment B raw27714step3 raw27714step3Labels := by
      have ha : raw27714step3 = -raw27714step2 := by apply Matrix.ext; change ∀ i j, raw27714step3 i j = -(raw27714step2 i j); unfold raw27714step3 raw27714step2; decide +kernel
      have hl : raw27714step3Labels = raw27714step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4374 node4374Labels := by rfl

def raw27715 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![4, -1, -3]]
def raw27715Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27715step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -2, 1], ![4, -1, -3]]
def raw27715step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27715step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 2, 1]]
def raw27715step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27715step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw27715step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27715 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27715 raw27715Labels = mixedMoment B node4367 node4367Labels := by
  calc
    mixedMoment B raw27715 raw27715Labels = mixedMoment B raw27715step0 raw27715step0Labels := by
      have hz : ∀ j, raw27715 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27715step0 = (fun i j => raw27715 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27715step0 raw27715; decide +kernel
      have hl : raw27715step0Labels = raw27715Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27715 raw27715Labels permutation434 hz
    mixedMoment B raw27715step0 raw27715step0Labels = mixedMoment B raw27715step1 raw27715step1Labels := by
      have ha : raw27715step1 = (fun i j => raw27715step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27715step1 raw27715step0; decide +kernel
      have hl : raw27715step1Labels = raw27715step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27715step0 raw27715step0Labels permutation151 permutation2
    mixedMoment B raw27715step1 raw27715step1Labels = mixedMoment B raw27715step2 raw27715step2Labels := by
      have ha : raw27715step2 = -raw27715step1 := by apply Matrix.ext; change ∀ i j, raw27715step2 i j = -(raw27715step1 i j); unfold raw27715step2 raw27715step1; decide +kernel
      have hl : raw27715step2Labels = raw27715step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4367 node4367Labels := by rfl

def raw27716 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![4, -1, -3]]
def raw27716Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27716step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -2, 1], ![4, -1, -3]]
def raw27716step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27716step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 2, 1]]
def raw27716step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27716step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw27716step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27716 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27716 raw27716Labels = mixedMoment B node4367 node4367Labels := by
  calc
    mixedMoment B raw27716 raw27716Labels = mixedMoment B raw27716step0 raw27716step0Labels := by
      have hz : ∀ j, raw27716 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27716step0 = (fun i j => raw27716 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27716step0 raw27716; decide +kernel
      have hl : raw27716step0Labels = raw27716Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27716 raw27716Labels permutation346 hz
    mixedMoment B raw27716step0 raw27716step0Labels = mixedMoment B raw27716step1 raw27716step1Labels := by
      have ha : raw27716step1 = (fun i j => raw27716step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27716step1 raw27716step0; decide +kernel
      have hl : raw27716step1Labels = raw27716step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27716step0 raw27716step0Labels permutation151 permutation2
    mixedMoment B raw27716step1 raw27716step1Labels = mixedMoment B raw27716step2 raw27716step2Labels := by
      have ha : raw27716step2 = -raw27716step1 := by apply Matrix.ext; change ∀ i j, raw27716step2 i j = -(raw27716step1 i j); unfold raw27716step2 raw27716step1; decide +kernel
      have hl : raw27716step2Labels = raw27716step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4367 node4367Labels := by rfl

def raw27717 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![4, -1, -3]]
def raw27717Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27717step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![4, -1, -3]]
def raw27717step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27717step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![4, -1, -3]]
def raw27717step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27717step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw27717step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27717step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27717step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27717 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27717 raw27717Labels = mixedMoment B node4463 node4463Labels := by
  calc
    mixedMoment B raw27717 raw27717Labels = mixedMoment B raw27717step0 raw27717step0Labels := by
      have hz : ∀ j, raw27717 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27717step0 = (fun i j => raw27717 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27717step0 raw27717; decide +kernel
      have hl : raw27717step0Labels = raw27717Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27717 raw27717Labels permutation434 hz
    mixedMoment B raw27717step0 raw27717step0Labels = mixedMoment B raw27717step1 raw27717step1Labels := by
      have hz : ∀ j, raw27717step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27717step1 = (fun i j => raw27717step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27717step1 raw27717step0; decide +kernel
      have hl : raw27717step1Labels = raw27717step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27717step0 raw27717step0Labels permutation80 hz
    mixedMoment B raw27717step1 raw27717step1Labels = mixedMoment B raw27717step2 raw27717step2Labels := by
      have ha : raw27717step2 = (fun i j => raw27717step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27717step2 raw27717step1; decide +kernel
      have hl : raw27717step2Labels = raw27717step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27717step1 raw27717step1Labels permutation31 permutation2
    mixedMoment B raw27717step2 raw27717step2Labels = mixedMoment B raw27717step3 raw27717step3Labels := by
      have ha : raw27717step3 = -raw27717step2 := by apply Matrix.ext; change ∀ i j, raw27717step3 i j = -(raw27717step2 i j); unfold raw27717step3 raw27717step2; decide +kernel
      have hl : raw27717step3Labels = raw27717step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4463 node4463Labels := by rfl

def raw27718 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw27718Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27718step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw27718step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27718step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -2, 1], ![3, 0, -3]]
def raw27718step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27718step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw27718step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27718step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw27718step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27718 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27718 raw27718Labels = mixedMoment B node2288 node2288Labels := by
  calc
    mixedMoment B raw27718 raw27718Labels = mixedMoment B raw27718step0 raw27718step0Labels := by
      have hz : ∀ j, raw27718 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27718step0 = (fun i j => raw27718 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27718step0 raw27718; decide +kernel
      have hl : raw27718step0Labels = raw27718Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27718 raw27718Labels permutation434 hz
    mixedMoment B raw27718step0 raw27718step0Labels = mixedMoment B raw27718step1 raw27718step1Labels := by
      have hz : ∀ j, raw27718step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27718step1 = (fun i j => raw27718step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27718step1 raw27718step0; decide +kernel
      have hl : raw27718step1Labels = raw27718step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27718step0 raw27718step0Labels permutation80 hz
    mixedMoment B raw27718step1 raw27718step1Labels = mixedMoment B raw27718step2 raw27718step2Labels := by
      have ha : raw27718step2 = (fun i j => raw27718step1 (permutation30 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27718step2 raw27718step1; decide +kernel
      have hl : raw27718step2Labels = raw27718step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27718step1 raw27718step1Labels permutation30 permutation7
    mixedMoment B raw27718step2 raw27718step2Labels = mixedMoment B raw27718step3 raw27718step3Labels := by
      have ha : raw27718step3 = raw27718step2 := by apply Matrix.ext; unfold raw27718step3 raw27718step2; decide +kernel
      have hl : raw27718step2Labels = labelEmbedding1 ∘ raw27718step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27718step2 raw27718step2Labels raw27718step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2288 node2288Labels := by rfl

def raw27719 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw27719Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27719step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw27719step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27719step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw27719step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27719step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw27719step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27719 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27719 raw27719Labels = mixedMoment B node2260 node2260Labels := by
  calc
    mixedMoment B raw27719 raw27719Labels = mixedMoment B raw27719step0 raw27719step0Labels := by
      have hz : ∀ j, raw27719 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27719step0 = (fun i j => raw27719 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27719step0 raw27719; decide +kernel
      have hl : raw27719step0Labels = raw27719Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27719 raw27719Labels permutation434 hz
    mixedMoment B raw27719step0 raw27719step0Labels = mixedMoment B raw27719step1 raw27719step1Labels := by
      have ha : raw27719step1 = (fun i j => raw27719step0 (permutation145 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27719step1 raw27719step0; decide +kernel
      have hl : raw27719step1Labels = raw27719step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27719step0 raw27719step0Labels permutation145 permutation7
    mixedMoment B raw27719step1 raw27719step1Labels = mixedMoment B raw27719step2 raw27719step2Labels := by
      have ha : raw27719step2 = raw27719step1 := by apply Matrix.ext; unfold raw27719step2 raw27719step1; decide +kernel
      have hl : raw27719step1Labels = labelEmbedding1 ∘ raw27719step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27719step1 raw27719step1Labels raw27719step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2260 node2260Labels := by rfl

def raw27720 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw27720Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27720step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw27720step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27720step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw27720step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27720step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw27720step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27720 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27720 raw27720Labels = mixedMoment B node2260 node2260Labels := by
  calc
    mixedMoment B raw27720 raw27720Labels = mixedMoment B raw27720step0 raw27720step0Labels := by
      have hz : ∀ j, raw27720 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27720step0 = (fun i j => raw27720 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27720step0 raw27720; decide +kernel
      have hl : raw27720step0Labels = raw27720Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27720 raw27720Labels permutation346 hz
    mixedMoment B raw27720step0 raw27720step0Labels = mixedMoment B raw27720step1 raw27720step1Labels := by
      have ha : raw27720step1 = (fun i j => raw27720step0 (permutation145 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27720step1 raw27720step0; decide +kernel
      have hl : raw27720step1Labels = raw27720step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27720step0 raw27720step0Labels permutation145 permutation7
    mixedMoment B raw27720step1 raw27720step1Labels = mixedMoment B raw27720step2 raw27720step2Labels := by
      have ha : raw27720step2 = raw27720step1 := by apply Matrix.ext; unfold raw27720step2 raw27720step1; decide +kernel
      have hl : raw27720step1Labels = labelEmbedding1 ∘ raw27720step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27720step1 raw27720step1Labels raw27720step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2260 node2260Labels := by rfl

def raw27721 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw27721Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27721step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw27721step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27721step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![3, 0, -3]]
def raw27721step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27721step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw27721step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27721step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw27721step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27721 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27721 raw27721Labels = mixedMoment B node2291 node2291Labels := by
  calc
    mixedMoment B raw27721 raw27721Labels = mixedMoment B raw27721step0 raw27721step0Labels := by
      have hz : ∀ j, raw27721 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27721step0 = (fun i j => raw27721 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27721step0 raw27721; decide +kernel
      have hl : raw27721step0Labels = raw27721Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27721 raw27721Labels permutation434 hz
    mixedMoment B raw27721step0 raw27721step0Labels = mixedMoment B raw27721step1 raw27721step1Labels := by
      have hz : ∀ j, raw27721step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27721step1 = (fun i j => raw27721step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27721step1 raw27721step0; decide +kernel
      have hl : raw27721step1Labels = raw27721step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27721step0 raw27721step0Labels permutation80 hz
    mixedMoment B raw27721step1 raw27721step1Labels = mixedMoment B raw27721step2 raw27721step2Labels := by
      have ha : raw27721step2 = (fun i j => raw27721step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27721step2 raw27721step1; decide +kernel
      have hl : raw27721step2Labels = raw27721step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27721step1 raw27721step1Labels permutation31 permutation7
    mixedMoment B raw27721step2 raw27721step2Labels = mixedMoment B raw27721step3 raw27721step3Labels := by
      have ha : raw27721step3 = raw27721step2 := by apply Matrix.ext; unfold raw27721step3 raw27721step2; decide +kernel
      have hl : raw27721step2Labels = labelEmbedding1 ∘ raw27721step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27721step2 raw27721step2Labels raw27721step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2291 node2291Labels := by rfl

def raw27722 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw27722Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27722step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw27722step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27722step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![2, 1, -3]]
def raw27722step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27722step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw27722step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27722step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw27722step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27722 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27722 raw27722Labels = mixedMoment B node2782 node2782Labels := by
  calc
    mixedMoment B raw27722 raw27722Labels = mixedMoment B raw27722step0 raw27722step0Labels := by
      have hz : ∀ j, raw27722 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27722step0 = (fun i j => raw27722 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27722step0 raw27722; decide +kernel
      have hl : raw27722step0Labels = raw27722Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27722 raw27722Labels permutation434 hz
    mixedMoment B raw27722step0 raw27722step0Labels = mixedMoment B raw27722step1 raw27722step1Labels := by
      have hz : ∀ j, raw27722step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27722step1 = (fun i j => raw27722step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27722step1 raw27722step0; decide +kernel
      have hl : raw27722step1Labels = raw27722step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27722step0 raw27722step0Labels permutation80 hz
    mixedMoment B raw27722step1 raw27722step1Labels = mixedMoment B raw27722step2 raw27722step2Labels := by
      have ha : raw27722step2 = (fun i j => raw27722step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27722step2 raw27722step1; decide +kernel
      have hl : raw27722step2Labels = raw27722step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27722step1 raw27722step1Labels permutation31 permutation7
    mixedMoment B raw27722step2 raw27722step2Labels = mixedMoment B raw27722step3 raw27722step3Labels := by
      have ha : raw27722step3 = raw27722step2 := by apply Matrix.ext; unfold raw27722step3 raw27722step2; decide +kernel
      have hl : raw27722step2Labels = labelEmbedding1 ∘ raw27722step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27722step2 raw27722step2Labels raw27722step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2782 node2782Labels := by rfl

def raw27723 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw27723Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27723step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw27723step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27723step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -2, 1], ![3, 0, -3]]
def raw27723step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27723step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -3, 3], ![-1, 1, 0], ![-2, 1, 1]]
def raw27723step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27723step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]
def raw27723step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27723step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]
def raw27723step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27723 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27723 raw27723Labels = mixedMoment B node1745 node1745Labels := by
  calc
    mixedMoment B raw27723 raw27723Labels = mixedMoment B raw27723step0 raw27723step0Labels := by
      have hz : ∀ j, raw27723 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27723step0 = (fun i j => raw27723 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27723step0 raw27723; decide +kernel
      have hl : raw27723step0Labels = raw27723Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27723 raw27723Labels permutation434 hz
    mixedMoment B raw27723step0 raw27723step0Labels = mixedMoment B raw27723step1 raw27723step1Labels := by
      have hz : ∀ j, raw27723step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27723step1 = (fun i j => raw27723step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27723step1 raw27723step0; decide +kernel
      have hl : raw27723step1Labels = raw27723step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27723step0 raw27723step0Labels permutation80 hz
    mixedMoment B raw27723step1 raw27723step1Labels = mixedMoment B raw27723step2 raw27723step2Labels := by
      have ha : raw27723step2 = (fun i j => raw27723step1 (permutation12 i) (permutation5 j)) := by apply Matrix.ext; unfold raw27723step2 raw27723step1; decide +kernel
      have hl : raw27723step2Labels = raw27723step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27723step1 raw27723step1Labels permutation12 permutation5
    mixedMoment B raw27723step2 raw27723step2Labels = mixedMoment B raw27723step3 raw27723step3Labels := by
      have ha : raw27723step3 = -raw27723step2 := by apply Matrix.ext; change ∀ i j, raw27723step3 i j = -(raw27723step2 i j); unfold raw27723step3 raw27723step2; decide +kernel
      have hl : raw27723step3Labels = raw27723step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27723step3 raw27723step3Labels = mixedMoment B raw27723step4 raw27723step4Labels := by
      have ha : raw27723step4 = raw27723step3 := by apply Matrix.ext; unfold raw27723step4 raw27723step3; decide +kernel
      have hl : raw27723step3Labels = labelEmbedding1 ∘ raw27723step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27723step3 raw27723step3Labels raw27723step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1745 node1745Labels := by rfl

def raw27724 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw27724Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27724step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw27724step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27724step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw27724step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27724step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw27724step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27724 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27724 raw27724Labels = mixedMoment B node2259 node2259Labels := by
  calc
    mixedMoment B raw27724 raw27724Labels = mixedMoment B raw27724step0 raw27724step0Labels := by
      have hz : ∀ j, raw27724 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27724step0 = (fun i j => raw27724 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27724step0 raw27724; decide +kernel
      have hl : raw27724step0Labels = raw27724Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27724 raw27724Labels permutation434 hz
    mixedMoment B raw27724step0 raw27724step0Labels = mixedMoment B raw27724step1 raw27724step1Labels := by
      have ha : raw27724step1 = (fun i j => raw27724step0 (permutation145 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27724step1 raw27724step0; decide +kernel
      have hl : raw27724step1Labels = raw27724step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27724step0 raw27724step0Labels permutation145 permutation7
    mixedMoment B raw27724step1 raw27724step1Labels = mixedMoment B raw27724step2 raw27724step2Labels := by
      have ha : raw27724step2 = raw27724step1 := by apply Matrix.ext; unfold raw27724step2 raw27724step1; decide +kernel
      have hl : raw27724step1Labels = labelEmbedding1 ∘ raw27724step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27724step1 raw27724step1Labels raw27724step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2259 node2259Labels := by rfl

def raw27725 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw27725Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27725step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw27725step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27725step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw27725step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27725step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw27725step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27725 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27725 raw27725Labels = mixedMoment B node2259 node2259Labels := by
  calc
    mixedMoment B raw27725 raw27725Labels = mixedMoment B raw27725step0 raw27725step0Labels := by
      have hz : ∀ j, raw27725 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27725step0 = (fun i j => raw27725 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27725step0 raw27725; decide +kernel
      have hl : raw27725step0Labels = raw27725Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27725 raw27725Labels permutation346 hz
    mixedMoment B raw27725step0 raw27725step0Labels = mixedMoment B raw27725step1 raw27725step1Labels := by
      have ha : raw27725step1 = (fun i j => raw27725step0 (permutation145 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27725step1 raw27725step0; decide +kernel
      have hl : raw27725step1Labels = raw27725step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27725step0 raw27725step0Labels permutation145 permutation7
    mixedMoment B raw27725step1 raw27725step1Labels = mixedMoment B raw27725step2 raw27725step2Labels := by
      have ha : raw27725step2 = raw27725step1 := by apply Matrix.ext; unfold raw27725step2 raw27725step1; decide +kernel
      have hl : raw27725step1Labels = labelEmbedding1 ∘ raw27725step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27725step1 raw27725step1Labels raw27725step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2259 node2259Labels := by rfl

def raw27726 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw27726Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27726step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw27726step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27726step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![3, 0, -3]]
def raw27726step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27726step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw27726step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27726step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw27726step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27726 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27726 raw27726Labels = mixedMoment B node2290 node2290Labels := by
  calc
    mixedMoment B raw27726 raw27726Labels = mixedMoment B raw27726step0 raw27726step0Labels := by
      have hz : ∀ j, raw27726 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27726step0 = (fun i j => raw27726 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27726step0 raw27726; decide +kernel
      have hl : raw27726step0Labels = raw27726Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27726 raw27726Labels permutation434 hz
    mixedMoment B raw27726step0 raw27726step0Labels = mixedMoment B raw27726step1 raw27726step1Labels := by
      have hz : ∀ j, raw27726step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27726step1 = (fun i j => raw27726step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27726step1 raw27726step0; decide +kernel
      have hl : raw27726step1Labels = raw27726step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27726step0 raw27726step0Labels permutation80 hz
    mixedMoment B raw27726step1 raw27726step1Labels = mixedMoment B raw27726step2 raw27726step2Labels := by
      have ha : raw27726step2 = (fun i j => raw27726step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27726step2 raw27726step1; decide +kernel
      have hl : raw27726step2Labels = raw27726step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27726step1 raw27726step1Labels permutation29 permutation7
    mixedMoment B raw27726step2 raw27726step2Labels = mixedMoment B raw27726step3 raw27726step3Labels := by
      have ha : raw27726step3 = raw27726step2 := by apply Matrix.ext; unfold raw27726step3 raw27726step2; decide +kernel
      have hl : raw27726step2Labels = labelEmbedding1 ∘ raw27726step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27726step2 raw27726step2Labels raw27726step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2290 node2290Labels := by rfl

def raw27727 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw27727Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27727step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw27727step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27727step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw27727step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27727step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw27727step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27727step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw27727step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27727 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27727 raw27727Labels = mixedMoment B node2781 node2781Labels := by
  calc
    mixedMoment B raw27727 raw27727Labels = mixedMoment B raw27727step0 raw27727step0Labels := by
      have hz : ∀ j, raw27727 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27727step0 = (fun i j => raw27727 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27727step0 raw27727; decide +kernel
      have hl : raw27727step0Labels = raw27727Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27727 raw27727Labels permutation434 hz
    mixedMoment B raw27727step0 raw27727step0Labels = mixedMoment B raw27727step1 raw27727step1Labels := by
      have hz : ∀ j, raw27727step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27727step1 = (fun i j => raw27727step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27727step1 raw27727step0; decide +kernel
      have hl : raw27727step1Labels = raw27727step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27727step0 raw27727step0Labels permutation80 hz
    mixedMoment B raw27727step1 raw27727step1Labels = mixedMoment B raw27727step2 raw27727step2Labels := by
      have ha : raw27727step2 = (fun i j => raw27727step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27727step2 raw27727step1; decide +kernel
      have hl : raw27727step2Labels = raw27727step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27727step1 raw27727step1Labels permutation31 permutation7
    mixedMoment B raw27727step2 raw27727step2Labels = mixedMoment B raw27727step3 raw27727step3Labels := by
      have ha : raw27727step3 = raw27727step2 := by apply Matrix.ext; unfold raw27727step3 raw27727step2; decide +kernel
      have hl : raw27727step2Labels = labelEmbedding1 ∘ raw27727step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27727step2 raw27727step2Labels raw27727step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2781 node2781Labels := by rfl

def raw27728 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw27728Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27728step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw27728step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27728step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -3, 3], ![-1, 0, 1], ![-2, 1, 1]]
def raw27728step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27728step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1], ![2, -1, -1]]
def raw27728step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27728step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1], ![2, -1, -1]]
def raw27728step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27728 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27728 raw27728Labels = mixedMoment B node1686 node1686Labels := by
  calc
    mixedMoment B raw27728 raw27728Labels = mixedMoment B raw27728step0 raw27728step0Labels := by
      have hz : ∀ j, raw27728 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27728step0 = (fun i j => raw27728 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27728step0 raw27728; decide +kernel
      have hl : raw27728step0Labels = raw27728Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27728 raw27728Labels permutation434 hz
    mixedMoment B raw27728step0 raw27728step0Labels = mixedMoment B raw27728step1 raw27728step1Labels := by
      have ha : raw27728step1 = (fun i j => raw27728step0 (permutation36 i) (permutation5 j)) := by apply Matrix.ext; unfold raw27728step1 raw27728step0; decide +kernel
      have hl : raw27728step1Labels = raw27728step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27728step0 raw27728step0Labels permutation36 permutation5
    mixedMoment B raw27728step1 raw27728step1Labels = mixedMoment B raw27728step2 raw27728step2Labels := by
      have ha : raw27728step2 = -raw27728step1 := by apply Matrix.ext; change ∀ i j, raw27728step2 i j = -(raw27728step1 i j); unfold raw27728step2 raw27728step1; decide +kernel
      have hl : raw27728step2Labels = raw27728step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27728step2 raw27728step2Labels = mixedMoment B raw27728step3 raw27728step3Labels := by
      have ha : raw27728step3 = raw27728step2 := by apply Matrix.ext; unfold raw27728step3 raw27728step2; decide +kernel
      have hl : raw27728step2Labels = labelEmbedding1 ∘ raw27728step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27728step2 raw27728step2Labels raw27728step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1686 node1686Labels := by rfl

def raw27729 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw27729Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27729step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw27729step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27729step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 2, -3]]
def raw27729step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27729step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 2, -3]]
def raw27729step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27729 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27729 raw27729Labels = mixedMoment B node2223 node2223Labels := by
  calc
    mixedMoment B raw27729 raw27729Labels = mixedMoment B raw27729step0 raw27729step0Labels := by
      have hz : ∀ j, raw27729 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27729step0 = (fun i j => raw27729 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27729step0 raw27729; decide +kernel
      have hl : raw27729step0Labels = raw27729Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27729 raw27729Labels permutation434 hz
    mixedMoment B raw27729step0 raw27729step0Labels = mixedMoment B raw27729step1 raw27729step1Labels := by
      have ha : raw27729step1 = (fun i j => raw27729step0 (permutation145 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27729step1 raw27729step0; decide +kernel
      have hl : raw27729step1Labels = raw27729step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27729step0 raw27729step0Labels permutation145 permutation7
    mixedMoment B raw27729step1 raw27729step1Labels = mixedMoment B raw27729step2 raw27729step2Labels := by
      have ha : raw27729step2 = raw27729step1 := by apply Matrix.ext; unfold raw27729step2 raw27729step1; decide +kernel
      have hl : raw27729step1Labels = labelEmbedding1 ∘ raw27729step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27729step1 raw27729step1Labels raw27729step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2223 node2223Labels := by rfl

def raw27730 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw27730Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27730step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw27730step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27730step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw27730step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27730 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27730 raw27730Labels = mixedMoment B node2198 node2198Labels := by
  calc
    mixedMoment B raw27730 raw27730Labels = mixedMoment B raw27730step0 raw27730step0Labels := by
      have ha : raw27730step0 = (fun i j => raw27730 (permutation640 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27730step0 raw27730; decide +kernel
      have hl : raw27730step0Labels = raw27730Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27730 raw27730Labels permutation640 permutation7
    mixedMoment B raw27730step0 raw27730step0Labels = mixedMoment B raw27730step1 raw27730step1Labels := by
      have ha : raw27730step1 = raw27730step0 := by apply Matrix.ext; unfold raw27730step1 raw27730step0; decide +kernel
      have hl : raw27730step0Labels = labelEmbedding1 ∘ raw27730step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27730step0 raw27730step0Labels raw27730step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2198 node2198Labels := by rfl

def raw27731 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw27731Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27731step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw27731step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27731step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw27731step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27731step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw27731step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27731 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27731 raw27731Labels = mixedMoment B node2224 node2224Labels := by
  calc
    mixedMoment B raw27731 raw27731Labels = mixedMoment B raw27731step0 raw27731step0Labels := by
      have hz : ∀ j, raw27731 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27731step0 = (fun i j => raw27731 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27731step0 raw27731; decide +kernel
      have hl : raw27731step0Labels = raw27731Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27731 raw27731Labels permutation434 hz
    mixedMoment B raw27731step0 raw27731step0Labels = mixedMoment B raw27731step1 raw27731step1Labels := by
      have ha : raw27731step1 = (fun i j => raw27731step0 (permutation145 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27731step1 raw27731step0; decide +kernel
      have hl : raw27731step1Labels = raw27731step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27731step0 raw27731step0Labels permutation145 permutation7
    mixedMoment B raw27731step1 raw27731step1Labels = mixedMoment B raw27731step2 raw27731step2Labels := by
      have ha : raw27731step2 = raw27731step1 := by apply Matrix.ext; unfold raw27731step2 raw27731step1; decide +kernel
      have hl : raw27731step1Labels = labelEmbedding1 ∘ raw27731step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27731step1 raw27731step1Labels raw27731step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2224 node2224Labels := by rfl

def raw27732 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw27732Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27732step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw27732step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27732step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw27732step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27732step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw27732step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27732 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27732 raw27732Labels = mixedMoment B node2735 node2735Labels := by
  calc
    mixedMoment B raw27732 raw27732Labels = mixedMoment B raw27732step0 raw27732step0Labels := by
      have hz : ∀ j, raw27732 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27732step0 = (fun i j => raw27732 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27732step0 raw27732; decide +kernel
      have hl : raw27732step0Labels = raw27732Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27732 raw27732Labels permutation434 hz
    mixedMoment B raw27732step0 raw27732step0Labels = mixedMoment B raw27732step1 raw27732step1Labels := by
      have ha : raw27732step1 = (fun i j => raw27732step0 (permutation145 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27732step1 raw27732step0; decide +kernel
      have hl : raw27732step1Labels = raw27732step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27732step0 raw27732step0Labels permutation145 permutation7
    mixedMoment B raw27732step1 raw27732step1Labels = mixedMoment B raw27732step2 raw27732step2Labels := by
      have ha : raw27732step2 = raw27732step1 := by apply Matrix.ext; unfold raw27732step2 raw27732step1; decide +kernel
      have hl : raw27732step1Labels = labelEmbedding1 ∘ raw27732step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27732step1 raw27732step1Labels raw27732step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2735 node2735Labels := by rfl

def raw27733 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw27733Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27733step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw27733step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27733step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -3, 3], ![-1, 0, 1], ![-2, 1, 1]]
def raw27733step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27733step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1], ![2, -1, -1]]
def raw27733step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27733step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1], ![2, -1, -1]]
def raw27733step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27733 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27733 raw27733Labels = mixedMoment B node1686 node1686Labels := by
  calc
    mixedMoment B raw27733 raw27733Labels = mixedMoment B raw27733step0 raw27733step0Labels := by
      have hz : ∀ j, raw27733 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27733step0 = (fun i j => raw27733 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27733step0 raw27733; decide +kernel
      have hl : raw27733step0Labels = raw27733Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27733 raw27733Labels permutation346 hz
    mixedMoment B raw27733step0 raw27733step0Labels = mixedMoment B raw27733step1 raw27733step1Labels := by
      have ha : raw27733step1 = (fun i j => raw27733step0 (permutation36 i) (permutation5 j)) := by apply Matrix.ext; unfold raw27733step1 raw27733step0; decide +kernel
      have hl : raw27733step1Labels = raw27733step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27733step0 raw27733step0Labels permutation36 permutation5
    mixedMoment B raw27733step1 raw27733step1Labels = mixedMoment B raw27733step2 raw27733step2Labels := by
      have ha : raw27733step2 = -raw27733step1 := by apply Matrix.ext; change ∀ i j, raw27733step2 i j = -(raw27733step1 i j); unfold raw27733step2 raw27733step1; decide +kernel
      have hl : raw27733step2Labels = raw27733step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27733step2 raw27733step2Labels = mixedMoment B raw27733step3 raw27733step3Labels := by
      have ha : raw27733step3 = raw27733step2 := by apply Matrix.ext; unfold raw27733step3 raw27733step2; decide +kernel
      have hl : raw27733step2Labels = labelEmbedding1 ∘ raw27733step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27733step2 raw27733step2Labels raw27733step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1686 node1686Labels := by rfl

def raw27734 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw27734Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27734step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw27734step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27734step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 2, -3]]
def raw27734step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27734step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 2, -3]]
def raw27734step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27734 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27734 raw27734Labels = mixedMoment B node2223 node2223Labels := by
  calc
    mixedMoment B raw27734 raw27734Labels = mixedMoment B raw27734step0 raw27734step0Labels := by
      have hz : ∀ j, raw27734 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27734step0 = (fun i j => raw27734 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27734step0 raw27734; decide +kernel
      have hl : raw27734step0Labels = raw27734Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27734 raw27734Labels permutation346 hz
    mixedMoment B raw27734step0 raw27734step0Labels = mixedMoment B raw27734step1 raw27734step1Labels := by
      have ha : raw27734step1 = (fun i j => raw27734step0 (permutation145 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27734step1 raw27734step0; decide +kernel
      have hl : raw27734step1Labels = raw27734step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27734step0 raw27734step0Labels permutation145 permutation7
    mixedMoment B raw27734step1 raw27734step1Labels = mixedMoment B raw27734step2 raw27734step2Labels := by
      have ha : raw27734step2 = raw27734step1 := by apply Matrix.ext; unfold raw27734step2 raw27734step1; decide +kernel
      have hl : raw27734step1Labels = labelEmbedding1 ∘ raw27734step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27734step1 raw27734step1Labels raw27734step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2223 node2223Labels := by rfl

def raw27735 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw27735Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27735step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw27735step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27735step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw27735step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27735 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27735 raw27735Labels = mixedMoment B node2198 node2198Labels := by
  calc
    mixedMoment B raw27735 raw27735Labels = mixedMoment B raw27735step0 raw27735step0Labels := by
      have ha : raw27735step0 = (fun i j => raw27735 (permutation658 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27735step0 raw27735; decide +kernel
      have hl : raw27735step0Labels = raw27735Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27735 raw27735Labels permutation658 permutation7
    mixedMoment B raw27735step0 raw27735step0Labels = mixedMoment B raw27735step1 raw27735step1Labels := by
      have ha : raw27735step1 = raw27735step0 := by apply Matrix.ext; unfold raw27735step1 raw27735step0; decide +kernel
      have hl : raw27735step0Labels = labelEmbedding1 ∘ raw27735step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27735step0 raw27735step0Labels raw27735step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2198 node2198Labels := by rfl

def raw27736 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw27736Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27736step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw27736step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27736step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw27736step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27736step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw27736step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27736 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27736 raw27736Labels = mixedMoment B node2224 node2224Labels := by
  calc
    mixedMoment B raw27736 raw27736Labels = mixedMoment B raw27736step0 raw27736step0Labels := by
      have hz : ∀ j, raw27736 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27736step0 = (fun i j => raw27736 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27736step0 raw27736; decide +kernel
      have hl : raw27736step0Labels = raw27736Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27736 raw27736Labels permutation346 hz
    mixedMoment B raw27736step0 raw27736step0Labels = mixedMoment B raw27736step1 raw27736step1Labels := by
      have ha : raw27736step1 = (fun i j => raw27736step0 (permutation145 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27736step1 raw27736step0; decide +kernel
      have hl : raw27736step1Labels = raw27736step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27736step0 raw27736step0Labels permutation145 permutation7
    mixedMoment B raw27736step1 raw27736step1Labels = mixedMoment B raw27736step2 raw27736step2Labels := by
      have ha : raw27736step2 = raw27736step1 := by apply Matrix.ext; unfold raw27736step2 raw27736step1; decide +kernel
      have hl : raw27736step1Labels = labelEmbedding1 ∘ raw27736step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27736step1 raw27736step1Labels raw27736step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2224 node2224Labels := by rfl

def raw27737 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw27737Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27737step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw27737step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27737step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw27737step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27737step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw27737step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27737 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27737 raw27737Labels = mixedMoment B node2735 node2735Labels := by
  calc
    mixedMoment B raw27737 raw27737Labels = mixedMoment B raw27737step0 raw27737step0Labels := by
      have hz : ∀ j, raw27737 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27737step0 = (fun i j => raw27737 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27737step0 raw27737; decide +kernel
      have hl : raw27737step0Labels = raw27737Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27737 raw27737Labels permutation346 hz
    mixedMoment B raw27737step0 raw27737step0Labels = mixedMoment B raw27737step1 raw27737step1Labels := by
      have ha : raw27737step1 = (fun i j => raw27737step0 (permutation145 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27737step1 raw27737step0; decide +kernel
      have hl : raw27737step1Labels = raw27737step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27737step0 raw27737step0Labels permutation145 permutation7
    mixedMoment B raw27737step1 raw27737step1Labels = mixedMoment B raw27737step2 raw27737step2Labels := by
      have ha : raw27737step2 = raw27737step1 := by apply Matrix.ext; unfold raw27737step2 raw27737step1; decide +kernel
      have hl : raw27737step1Labels = labelEmbedding1 ∘ raw27737step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27737step1 raw27737step1Labels raw27737step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2735 node2735Labels := by rfl

def raw27738 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![3, 0, -3]]
def raw27738Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27738step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![2, -3, 1], ![3, 0, -3]]
def raw27738step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27738step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![2, -3, 1], ![3, 0, -3]]
def raw27738step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27738step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -3, 3], ![-3, 1, 2]]
def raw27738step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27738step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 3, -3], ![3, -1, -2]]
def raw27738step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27738step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 3, -3], ![3, -1, -2]]
def raw27738step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27738 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27738 raw27738Labels = mixedMoment B node1687 node1687Labels := by
  calc
    mixedMoment B raw27738 raw27738Labels = mixedMoment B raw27738step0 raw27738step0Labels := by
      have hz : ∀ j, raw27738 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27738step0 = (fun i j => raw27738 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27738step0 raw27738; decide +kernel
      have hl : raw27738step0Labels = raw27738Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27738 raw27738Labels permutation434 hz
    mixedMoment B raw27738step0 raw27738step0Labels = mixedMoment B raw27738step1 raw27738step1Labels := by
      have hz : ∀ j, raw27738step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27738step1 = (fun i j => raw27738step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27738step1 raw27738step0; decide +kernel
      have hl : raw27738step1Labels = raw27738step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27738step0 raw27738step0Labels permutation80 hz
    mixedMoment B raw27738step1 raw27738step1Labels = mixedMoment B raw27738step2 raw27738step2Labels := by
      have ha : raw27738step2 = (fun i j => raw27738step1 (permutation9 i) (permutation5 j)) := by apply Matrix.ext; unfold raw27738step2 raw27738step1; decide +kernel
      have hl : raw27738step2Labels = raw27738step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27738step1 raw27738step1Labels permutation9 permutation5
    mixedMoment B raw27738step2 raw27738step2Labels = mixedMoment B raw27738step3 raw27738step3Labels := by
      have ha : raw27738step3 = -raw27738step2 := by apply Matrix.ext; change ∀ i j, raw27738step3 i j = -(raw27738step2 i j); unfold raw27738step3 raw27738step2; decide +kernel
      have hl : raw27738step3Labels = raw27738step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27738step3 raw27738step3Labels = mixedMoment B raw27738step4 raw27738step4Labels := by
      have ha : raw27738step4 = raw27738step3 := by apply Matrix.ext; unfold raw27738step4 raw27738step3; decide +kernel
      have hl : raw27738step3Labels = labelEmbedding1 ∘ raw27738step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27738step3 raw27738step3Labels raw27738step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1687 node1687Labels := by rfl

def raw27739 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![3, 0, -3]]
def raw27739Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27739step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![2, -3, 1], ![3, 0, -3]]
def raw27739step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27739step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![2, -3, 1], ![3, 0, -3]]
def raw27739step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27739step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -3, 2], ![1, 1, -2], ![1, 2, -3]]
def raw27739step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27739step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -3, 2], ![1, 1, -2], ![1, 2, -3]]
def raw27739step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27739 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27739 raw27739Labels = mixedMoment B node2286 node2286Labels := by
  calc
    mixedMoment B raw27739 raw27739Labels = mixedMoment B raw27739step0 raw27739step0Labels := by
      have hz : ∀ j, raw27739 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27739step0 = (fun i j => raw27739 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27739step0 raw27739; decide +kernel
      have hl : raw27739step0Labels = raw27739Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27739 raw27739Labels permutation434 hz
    mixedMoment B raw27739step0 raw27739step0Labels = mixedMoment B raw27739step1 raw27739step1Labels := by
      have hz : ∀ j, raw27739step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27739step1 = (fun i j => raw27739step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27739step1 raw27739step0; decide +kernel
      have hl : raw27739step1Labels = raw27739step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27739step0 raw27739step0Labels permutation80 hz
    mixedMoment B raw27739step1 raw27739step1Labels = mixedMoment B raw27739step2 raw27739step2Labels := by
      have ha : raw27739step2 = (fun i j => raw27739step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27739step2 raw27739step1; decide +kernel
      have hl : raw27739step2Labels = raw27739step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27739step1 raw27739step1Labels permutation31 permutation7
    mixedMoment B raw27739step2 raw27739step2Labels = mixedMoment B raw27739step3 raw27739step3Labels := by
      have ha : raw27739step3 = raw27739step2 := by apply Matrix.ext; unfold raw27739step3 raw27739step2; decide +kernel
      have hl : raw27739step2Labels = labelEmbedding1 ∘ raw27739step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27739step2 raw27739step2Labels raw27739step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2286 node2286Labels := by rfl

def raw27740 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![3, 0, -3]]
def raw27740Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27740step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![2, -3, 1], ![3, 0, -3]]
def raw27740step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27740step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 2, -3]]
def raw27740step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27740step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 2, -3]]
def raw27740step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27740 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27740 raw27740Labels = mixedMoment B node2256 node2256Labels := by
  calc
    mixedMoment B raw27740 raw27740Labels = mixedMoment B raw27740step0 raw27740step0Labels := by
      have hz : ∀ j, raw27740 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27740step0 = (fun i j => raw27740 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27740step0 raw27740; decide +kernel
      have hl : raw27740step0Labels = raw27740Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27740 raw27740Labels permutation434 hz
    mixedMoment B raw27740step0 raw27740step0Labels = mixedMoment B raw27740step1 raw27740step1Labels := by
      have ha : raw27740step1 = (fun i j => raw27740step0 (permutation145 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27740step1 raw27740step0; decide +kernel
      have hl : raw27740step1Labels = raw27740step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27740step0 raw27740step0Labels permutation145 permutation7
    mixedMoment B raw27740step1 raw27740step1Labels = mixedMoment B raw27740step2 raw27740step2Labels := by
      have ha : raw27740step2 = raw27740step1 := by apply Matrix.ext; unfold raw27740step2 raw27740step1; decide +kernel
      have hl : raw27740step1Labels = labelEmbedding1 ∘ raw27740step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27740step1 raw27740step1Labels raw27740step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2256 node2256Labels := by rfl

def raw27741 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![3, 0, -3]]
def raw27741Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27741step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![2, -3, 1], ![3, 0, -3]]
def raw27741step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27741step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 2, -3]]
def raw27741step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27741step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 2, -3]]
def raw27741step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27741 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27741 raw27741Labels = mixedMoment B node2256 node2256Labels := by
  calc
    mixedMoment B raw27741 raw27741Labels = mixedMoment B raw27741step0 raw27741step0Labels := by
      have hz : ∀ j, raw27741 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27741step0 = (fun i j => raw27741 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27741step0 raw27741; decide +kernel
      have hl : raw27741step0Labels = raw27741Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27741 raw27741Labels permutation346 hz
    mixedMoment B raw27741step0 raw27741step0Labels = mixedMoment B raw27741step1 raw27741step1Labels := by
      have ha : raw27741step1 = (fun i j => raw27741step0 (permutation145 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27741step1 raw27741step0; decide +kernel
      have hl : raw27741step1Labels = raw27741step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27741step0 raw27741step0Labels permutation145 permutation7
    mixedMoment B raw27741step1 raw27741step1Labels = mixedMoment B raw27741step2 raw27741step2Labels := by
      have ha : raw27741step2 = raw27741step1 := by apply Matrix.ext; unfold raw27741step2 raw27741step1; decide +kernel
      have hl : raw27741step1Labels = labelEmbedding1 ∘ raw27741step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27741step1 raw27741step1Labels raw27741step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2256 node2256Labels := by rfl

def raw27742 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![2, 1, -3]]
def raw27742Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27742step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![2, -3, 1], ![2, 1, -3]]
def raw27742step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27742step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -3, 1], ![2, 1, -3]]
def raw27742step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27742step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -3, 2], ![2, 1, -3]]
def raw27742step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27742step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -3, 2], ![2, 1, -3]]
def raw27742step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27742 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27742 raw27742Labels = mixedMoment B node2761 node2761Labels := by
  calc
    mixedMoment B raw27742 raw27742Labels = mixedMoment B raw27742step0 raw27742step0Labels := by
      have hz : ∀ j, raw27742 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27742step0 = (fun i j => raw27742 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27742step0 raw27742; decide +kernel
      have hl : raw27742step0Labels = raw27742Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27742 raw27742Labels permutation434 hz
    mixedMoment B raw27742step0 raw27742step0Labels = mixedMoment B raw27742step1 raw27742step1Labels := by
      have hz : ∀ j, raw27742step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27742step1 = (fun i j => raw27742step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27742step1 raw27742step0; decide +kernel
      have hl : raw27742step1Labels = raw27742step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27742step0 raw27742step0Labels permutation80 hz
    mixedMoment B raw27742step1 raw27742step1Labels = mixedMoment B raw27742step2 raw27742step2Labels := by
      have ha : raw27742step2 = (fun i j => raw27742step1 (permutation23 i) (permutation5 j)) := by apply Matrix.ext; unfold raw27742step2 raw27742step1; decide +kernel
      have hl : raw27742step2Labels = raw27742step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27742step1 raw27742step1Labels permutation23 permutation5
    mixedMoment B raw27742step2 raw27742step2Labels = mixedMoment B raw27742step3 raw27742step3Labels := by
      have ha : raw27742step3 = raw27742step2 := by apply Matrix.ext; unfold raw27742step3 raw27742step2; decide +kernel
      have hl : raw27742step2Labels = labelEmbedding1 ∘ raw27742step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27742step2 raw27742step2Labels raw27742step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2761 node2761Labels := by rfl

def raw27743 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![4, -1, -3]]
def raw27743Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27743step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![4, -1, -3]]
def raw27743step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27743step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -2, 1], ![4, -1, -3]]
def raw27743step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27743step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![-1, -3, 4], ![-2, 1, 1]]
def raw27743step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27743step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 3, -4], ![2, -1, -1]]
def raw27743step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27743step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 3, -4], ![2, -1, -1]]
def raw27743step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27743 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27743 raw27743Labels = mixedMoment B node1695 node1695Labels := by
  calc
    mixedMoment B raw27743 raw27743Labels = mixedMoment B raw27743step0 raw27743step0Labels := by
      have hz : ∀ j, raw27743 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27743step0 = (fun i j => raw27743 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27743step0 raw27743; decide +kernel
      have hl : raw27743step0Labels = raw27743Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27743 raw27743Labels permutation434 hz
    mixedMoment B raw27743step0 raw27743step0Labels = mixedMoment B raw27743step1 raw27743step1Labels := by
      have hz : ∀ j, raw27743step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27743step1 = (fun i j => raw27743step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27743step1 raw27743step0; decide +kernel
      have hl : raw27743step1Labels = raw27743step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27743step0 raw27743step0Labels permutation80 hz
    mixedMoment B raw27743step1 raw27743step1Labels = mixedMoment B raw27743step2 raw27743step2Labels := by
      have ha : raw27743step2 = (fun i j => raw27743step1 (permutation9 i) (permutation5 j)) := by apply Matrix.ext; unfold raw27743step2 raw27743step1; decide +kernel
      have hl : raw27743step2Labels = raw27743step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27743step1 raw27743step1Labels permutation9 permutation5
    mixedMoment B raw27743step2 raw27743step2Labels = mixedMoment B raw27743step3 raw27743step3Labels := by
      have ha : raw27743step3 = -raw27743step2 := by apply Matrix.ext; change ∀ i j, raw27743step3 i j = -(raw27743step2 i j); unfold raw27743step3 raw27743step2; decide +kernel
      have hl : raw27743step3Labels = raw27743step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27743step3 raw27743step3Labels = mixedMoment B raw27743step4 raw27743step4Labels := by
      have ha : raw27743step4 = raw27743step3 := by apply Matrix.ext; unfold raw27743step4 raw27743step3; decide +kernel
      have hl : raw27743step3Labels = labelEmbedding1 ∘ raw27743step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27743step3 raw27743step3Labels raw27743step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1695 node1695Labels := by rfl

def raw27744 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![4, -1, -3]]
def raw27744Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27744step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![1, -2, 1], ![4, -1, -3]]
def raw27744step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27744step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -2, 1], ![4, -1, -3]]
def raw27744step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27744step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -2, 1], ![1, 1, -2], ![1, 2, -3]]
def raw27744step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27744step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -2, 1], ![1, 1, -2], ![1, 2, -3]]
def raw27744step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27744 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27744 raw27744Labels = mixedMoment B node1748 node1748Labels := by
  calc
    mixedMoment B raw27744 raw27744Labels = mixedMoment B raw27744step0 raw27744step0Labels := by
      have hz : ∀ j, raw27744 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27744step0 = (fun i j => raw27744 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27744step0 raw27744; decide +kernel
      have hl : raw27744step0Labels = raw27744Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27744 raw27744Labels permutation434 hz
    mixedMoment B raw27744step0 raw27744step0Labels = mixedMoment B raw27744step1 raw27744step1Labels := by
      have hz : ∀ j, raw27744step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27744step1 = (fun i j => raw27744step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27744step1 raw27744step0; decide +kernel
      have hl : raw27744step1Labels = raw27744step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27744step0 raw27744step0Labels permutation80 hz
    mixedMoment B raw27744step1 raw27744step1Labels = mixedMoment B raw27744step2 raw27744step2Labels := by
      have ha : raw27744step2 = (fun i j => raw27744step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27744step2 raw27744step1; decide +kernel
      have hl : raw27744step2Labels = raw27744step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27744step1 raw27744step1Labels permutation31 permutation7
    mixedMoment B raw27744step2 raw27744step2Labels = mixedMoment B raw27744step3 raw27744step3Labels := by
      have ha : raw27744step3 = raw27744step2 := by apply Matrix.ext; unfold raw27744step3 raw27744step2; decide +kernel
      have hl : raw27744step2Labels = labelEmbedding1 ∘ raw27744step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27744step2 raw27744step2Labels raw27744step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1748 node1748Labels := by rfl

def raw27745 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![4, -1, -3]]
def raw27745Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27745step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -2, 1], ![4, -1, -3]]
def raw27745step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27745step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw27745step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27745step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw27745step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27745 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27745 raw27745Labels = mixedMoment B node1720 node1720Labels := by
  calc
    mixedMoment B raw27745 raw27745Labels = mixedMoment B raw27745step0 raw27745step0Labels := by
      have hz : ∀ j, raw27745 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27745step0 = (fun i j => raw27745 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27745step0 raw27745; decide +kernel
      have hl : raw27745step0Labels = raw27745Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27745 raw27745Labels permutation434 hz
    mixedMoment B raw27745step0 raw27745step0Labels = mixedMoment B raw27745step1 raw27745step1Labels := by
      have ha : raw27745step1 = (fun i j => raw27745step0 (permutation145 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27745step1 raw27745step0; decide +kernel
      have hl : raw27745step1Labels = raw27745step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27745step0 raw27745step0Labels permutation145 permutation7
    mixedMoment B raw27745step1 raw27745step1Labels = mixedMoment B raw27745step2 raw27745step2Labels := by
      have ha : raw27745step2 = raw27745step1 := by apply Matrix.ext; unfold raw27745step2 raw27745step1; decide +kernel
      have hl : raw27745step1Labels = labelEmbedding1 ∘ raw27745step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27745step1 raw27745step1Labels raw27745step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1720 node1720Labels := by rfl

def raw27746 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![4, -1, -3]]
def raw27746Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27746step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -2, 1], ![4, -1, -3]]
def raw27746step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27746step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw27746step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27746step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw27746step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27746 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27746 raw27746Labels = mixedMoment B node1720 node1720Labels := by
  calc
    mixedMoment B raw27746 raw27746Labels = mixedMoment B raw27746step0 raw27746step0Labels := by
      have hz : ∀ j, raw27746 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27746step0 = (fun i j => raw27746 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27746step0 raw27746; decide +kernel
      have hl : raw27746step0Labels = raw27746Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27746 raw27746Labels permutation346 hz
    mixedMoment B raw27746step0 raw27746step0Labels = mixedMoment B raw27746step1 raw27746step1Labels := by
      have ha : raw27746step1 = (fun i j => raw27746step0 (permutation145 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27746step1 raw27746step0; decide +kernel
      have hl : raw27746step1Labels = raw27746step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27746step0 raw27746step0Labels permutation145 permutation7
    mixedMoment B raw27746step1 raw27746step1Labels = mixedMoment B raw27746step2 raw27746step2Labels := by
      have ha : raw27746step2 = raw27746step1 := by apply Matrix.ext; unfold raw27746step2 raw27746step1; decide +kernel
      have hl : raw27746step1Labels = labelEmbedding1 ∘ raw27746step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27746step1 raw27746step1Labels raw27746step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1720 node1720Labels := by rfl

def raw27747 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![4, -1, -3]]
def raw27747Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27747step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![4, -1, -3]]
def raw27747step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27747step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![4, -1, -3]]
def raw27747step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27747step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw27747step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27747step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw27747step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27747 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27747 raw27747Labels = mixedMoment B node1750 node1750Labels := by
  calc
    mixedMoment B raw27747 raw27747Labels = mixedMoment B raw27747step0 raw27747step0Labels := by
      have hz : ∀ j, raw27747 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27747step0 = (fun i j => raw27747 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27747step0 raw27747; decide +kernel
      have hl : raw27747step0Labels = raw27747Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27747 raw27747Labels permutation434 hz
    mixedMoment B raw27747step0 raw27747step0Labels = mixedMoment B raw27747step1 raw27747step1Labels := by
      have hz : ∀ j, raw27747step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27747step1 = (fun i j => raw27747step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27747step1 raw27747step0; decide +kernel
      have hl : raw27747step1Labels = raw27747step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27747step0 raw27747step0Labels permutation80 hz
    mixedMoment B raw27747step1 raw27747step1Labels = mixedMoment B raw27747step2 raw27747step2Labels := by
      have ha : raw27747step2 = (fun i j => raw27747step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27747step2 raw27747step1; decide +kernel
      have hl : raw27747step2Labels = raw27747step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27747step1 raw27747step1Labels permutation31 permutation7
    mixedMoment B raw27747step2 raw27747step2Labels = mixedMoment B raw27747step3 raw27747step3Labels := by
      have ha : raw27747step3 = raw27747step2 := by apply Matrix.ext; unfold raw27747step3 raw27747step2; decide +kernel
      have hl : raw27747step2Labels = labelEmbedding1 ∘ raw27747step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27747step2 raw27747step2Labels raw27747step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1750 node1750Labels := by rfl

def raw27748 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw27748Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27748step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw27748step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27748step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -2, 1], ![3, 0, -3]]
def raw27748step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27748step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw27748step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27748step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw27748step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27748 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27748 raw27748Labels = mixedMoment B node2116 node2116Labels := by
  calc
    mixedMoment B raw27748 raw27748Labels = mixedMoment B raw27748step0 raw27748step0Labels := by
      have hz : ∀ j, raw27748 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27748step0 = (fun i j => raw27748 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27748step0 raw27748; decide +kernel
      have hl : raw27748step0Labels = raw27748Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27748 raw27748Labels permutation434 hz
    mixedMoment B raw27748step0 raw27748step0Labels = mixedMoment B raw27748step1 raw27748step1Labels := by
      have hz : ∀ j, raw27748step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27748step1 = (fun i j => raw27748step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27748step1 raw27748step0; decide +kernel
      have hl : raw27748step1Labels = raw27748step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27748step0 raw27748step0Labels permutation80 hz
    mixedMoment B raw27748step1 raw27748step1Labels = mixedMoment B raw27748step2 raw27748step2Labels := by
      have ha : raw27748step2 = (fun i j => raw27748step1 (permutation30 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27748step2 raw27748step1; decide +kernel
      have hl : raw27748step2Labels = raw27748step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27748step1 raw27748step1Labels permutation30 permutation2
    mixedMoment B raw27748step2 raw27748step2Labels = mixedMoment B raw27748step3 raw27748step3Labels := by
      have ha : raw27748step3 = -raw27748step2 := by apply Matrix.ext; change ∀ i j, raw27748step3 i j = -(raw27748step2 i j); unfold raw27748step3 raw27748step2; decide +kernel
      have hl : raw27748step3Labels = raw27748step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2116 node2116Labels := by rfl

def raw27749 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw27749Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27749step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw27749step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27749step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![3, 0, -3]]
def raw27749step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27749step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw27749step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27749step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27749step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27749 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27749 raw27749Labels = mixedMoment B node2112 node2112Labels := by
  calc
    mixedMoment B raw27749 raw27749Labels = mixedMoment B raw27749step0 raw27749step0Labels := by
      have hz : ∀ j, raw27749 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27749step0 = (fun i j => raw27749 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27749step0 raw27749; decide +kernel
      have hl : raw27749step0Labels = raw27749Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27749 raw27749Labels permutation434 hz
    mixedMoment B raw27749step0 raw27749step0Labels = mixedMoment B raw27749step1 raw27749step1Labels := by
      have hz : ∀ j, raw27749step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27749step1 = (fun i j => raw27749step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27749step1 raw27749step0; decide +kernel
      have hl : raw27749step1Labels = raw27749step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27749step0 raw27749step0Labels permutation80 hz
    mixedMoment B raw27749step1 raw27749step1Labels = mixedMoment B raw27749step2 raw27749step2Labels := by
      have ha : raw27749step2 = (fun i j => raw27749step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27749step2 raw27749step1; decide +kernel
      have hl : raw27749step2Labels = raw27749step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27749step1 raw27749step1Labels permutation31 permutation2
    mixedMoment B raw27749step2 raw27749step2Labels = mixedMoment B raw27749step3 raw27749step3Labels := by
      have ha : raw27749step3 = -raw27749step2 := by apply Matrix.ext; change ∀ i j, raw27749step3 i j = -(raw27749step2 i j); unfold raw27749step3 raw27749step2; decide +kernel
      have hl : raw27749step3Labels = raw27749step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2112 node2112Labels := by rfl

def raw27750 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw27750Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27750step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw27750step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27750step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -2, 1], ![-2, 1, 1], ![-3, 2, 1]]
def raw27750step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27750step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, -1, -1], ![3, -2, -1]]
def raw27750step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27750 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27750 raw27750Labels = mixedMoment B node1979 node1979Labels := by
  calc
    mixedMoment B raw27750 raw27750Labels = mixedMoment B raw27750step0 raw27750step0Labels := by
      have hz : ∀ j, raw27750 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27750step0 = (fun i j => raw27750 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27750step0 raw27750; decide +kernel
      have hl : raw27750step0Labels = raw27750Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27750 raw27750Labels permutation434 hz
    mixedMoment B raw27750step0 raw27750step0Labels = mixedMoment B raw27750step1 raw27750step1Labels := by
      have ha : raw27750step1 = (fun i j => raw27750step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27750step1 raw27750step0; decide +kernel
      have hl : raw27750step1Labels = raw27750step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27750step0 raw27750step0Labels permutation145 permutation2
    mixedMoment B raw27750step1 raw27750step1Labels = mixedMoment B raw27750step2 raw27750step2Labels := by
      have ha : raw27750step2 = -raw27750step1 := by apply Matrix.ext; change ∀ i j, raw27750step2 i j = -(raw27750step1 i j); unfold raw27750step2 raw27750step1; decide +kernel
      have hl : raw27750step2Labels = raw27750step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1979 node1979Labels := by rfl

def raw27751 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw27751Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27751step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw27751step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27751step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -2, 1], ![-2, 1, 1], ![-3, 2, 1]]
def raw27751step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27751step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, -1, -1], ![3, -2, -1]]
def raw27751step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27751 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27751 raw27751Labels = mixedMoment B node1979 node1979Labels := by
  calc
    mixedMoment B raw27751 raw27751Labels = mixedMoment B raw27751step0 raw27751step0Labels := by
      have hz : ∀ j, raw27751 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27751step0 = (fun i j => raw27751 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27751step0 raw27751; decide +kernel
      have hl : raw27751step0Labels = raw27751Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27751 raw27751Labels permutation346 hz
    mixedMoment B raw27751step0 raw27751step0Labels = mixedMoment B raw27751step1 raw27751step1Labels := by
      have ha : raw27751step1 = (fun i j => raw27751step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27751step1 raw27751step0; decide +kernel
      have hl : raw27751step1Labels = raw27751step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27751step0 raw27751step0Labels permutation145 permutation2
    mixedMoment B raw27751step1 raw27751step1Labels = mixedMoment B raw27751step2 raw27751step2Labels := by
      have ha : raw27751step2 = -raw27751step1 := by apply Matrix.ext; change ∀ i j, raw27751step2 i j = -(raw27751step1 i j); unfold raw27751step2 raw27751step1; decide +kernel
      have hl : raw27751step2Labels = raw27751step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1979 node1979Labels := by rfl

def raw27752 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![3, 0, -3]]
def raw27752Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27752step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![2, -3, 1], ![3, 0, -3]]
def raw27752step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27752step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![2, -3, 1], ![3, 0, -3]]
def raw27752step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27752step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![2, -3, 1], ![-2, 1, 1], ![-3, 2, 1]]
def raw27752step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27752step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![2, -1, -1], ![3, -2, -1]]
def raw27752step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27752 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27752 raw27752Labels = mixedMoment B node1831 node1831Labels := by
  calc
    mixedMoment B raw27752 raw27752Labels = mixedMoment B raw27752step0 raw27752step0Labels := by
      have hz : ∀ j, raw27752 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27752step0 = (fun i j => raw27752 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27752step0 raw27752; decide +kernel
      have hl : raw27752step0Labels = raw27752Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27752 raw27752Labels permutation434 hz
    mixedMoment B raw27752step0 raw27752step0Labels = mixedMoment B raw27752step1 raw27752step1Labels := by
      have hz : ∀ j, raw27752step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27752step1 = (fun i j => raw27752step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27752step1 raw27752step0; decide +kernel
      have hl : raw27752step1Labels = raw27752step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27752step0 raw27752step0Labels permutation80 hz
    mixedMoment B raw27752step1 raw27752step1Labels = mixedMoment B raw27752step2 raw27752step2Labels := by
      have ha : raw27752step2 = (fun i j => raw27752step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27752step2 raw27752step1; decide +kernel
      have hl : raw27752step2Labels = raw27752step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27752step1 raw27752step1Labels permutation31 permutation2
    mixedMoment B raw27752step2 raw27752step2Labels = mixedMoment B raw27752step3 raw27752step3Labels := by
      have ha : raw27752step3 = -raw27752step2 := by apply Matrix.ext; change ∀ i j, raw27752step3 i j = -(raw27752step2 i j); unfold raw27752step3 raw27752step2; decide +kernel
      have hl : raw27752step3Labels = raw27752step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1831 node1831Labels := by rfl

def raw27753 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![4, -1, -3]]
def raw27753Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27753step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![1, -2, 1], ![4, -1, -3]]
def raw27753step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27753step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -2, 1], ![4, -1, -3]]
def raw27753step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27753step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![1, -2, 1], ![-2, 1, 1], ![-3, 2, 1]]
def raw27753step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27753step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![2, -1, -1], ![3, -2, -1]]
def raw27753step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27753 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27753 raw27753Labels = mixedMoment B node953 node953Labels := by
  calc
    mixedMoment B raw27753 raw27753Labels = mixedMoment B raw27753step0 raw27753step0Labels := by
      have hz : ∀ j, raw27753 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27753step0 = (fun i j => raw27753 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27753step0 raw27753; decide +kernel
      have hl : raw27753step0Labels = raw27753Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27753 raw27753Labels permutation434 hz
    mixedMoment B raw27753step0 raw27753step0Labels = mixedMoment B raw27753step1 raw27753step1Labels := by
      have hz : ∀ j, raw27753step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27753step1 = (fun i j => raw27753step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27753step1 raw27753step0; decide +kernel
      have hl : raw27753step1Labels = raw27753step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27753step0 raw27753step0Labels permutation80 hz
    mixedMoment B raw27753step1 raw27753step1Labels = mixedMoment B raw27753step2 raw27753step2Labels := by
      have ha : raw27753step2 = (fun i j => raw27753step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27753step2 raw27753step1; decide +kernel
      have hl : raw27753step2Labels = raw27753step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27753step1 raw27753step1Labels permutation31 permutation2
    mixedMoment B raw27753step2 raw27753step2Labels = mixedMoment B raw27753step3 raw27753step3Labels := by
      have ha : raw27753step3 = -raw27753step2 := by apply Matrix.ext; change ∀ i j, raw27753step3 i j = -(raw27753step2 i j); unfold raw27753step3 raw27753step2; decide +kernel
      have hl : raw27753step3Labels = raw27753step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node953 node953Labels := by rfl

def raw27754 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![0, 0], ![0, 0], ![-1, 1], ![3, -3]]
def raw27754Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27754step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![0, 0], ![-1, 1], ![3, -3]]
def raw27754step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27754step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![3, -3]]
def raw27754step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27754step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![3, -3], ![-1, 1], ![-1, 1], ![-1, 1]]
def raw27754step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27754step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]
def raw27754step3Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical27754 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27754 raw27754Labels = mixedMoment B node4083 node4083Labels := by
  calc
    mixedMoment B raw27754 raw27754Labels = mixedMoment B raw27754step0 raw27754step0Labels := by
      have hz : ∀ j, raw27754 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27754step0 = (fun i j => raw27754 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27754step0 raw27754; decide +kernel
      have hl : raw27754step0Labels = raw27754Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27754 raw27754Labels permutation434 hz
    mixedMoment B raw27754step0 raw27754step0Labels = mixedMoment B raw27754step1 raw27754step1Labels := by
      have hz : ∀ j, raw27754step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27754step1 = (fun i j => raw27754step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27754step1 raw27754step0; decide +kernel
      have hl : raw27754step1Labels = raw27754step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27754step0 raw27754step0Labels permutation80 hz
    mixedMoment B raw27754step1 raw27754step1Labels = mixedMoment B raw27754step2 raw27754step2Labels := by
      have ha : raw27754step2 = (fun i j => raw27754step1 (permutation26 i) (permutation0 j)) := by apply Matrix.ext; unfold raw27754step2 raw27754step1; decide +kernel
      have hl : raw27754step2Labels = raw27754step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27754step1 raw27754step1Labels permutation26 permutation0
    mixedMoment B raw27754step2 raw27754step2Labels = mixedMoment B raw27754step3 raw27754step3Labels := by
      have ha : raw27754step3 = -raw27754step2 := by apply Matrix.ext; change ∀ i j, raw27754step3 i j = -(raw27754step2 i j); unfold raw27754step3 raw27754step2; decide +kernel
      have hl : raw27754step3Labels = raw27754step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4083 node4083Labels := by rfl

def raw27755 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw27755Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27755step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw27755step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27755step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw27755step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27755 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27755 raw27755Labels = mixedMoment B node1336 node1336Labels := by
  calc
    mixedMoment B raw27755 raw27755Labels = mixedMoment B raw27755step0 raw27755step0Labels := by
      have hz : ∀ j, raw27755 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27755step0 = (fun i j => raw27755 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27755step0 raw27755; decide +kernel
      have hl : raw27755step0Labels = raw27755Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27755 raw27755Labels permutation434 hz
    mixedMoment B raw27755step0 raw27755step0Labels = mixedMoment B raw27755step1 raw27755step1Labels := by
      have ha : raw27755step1 = (fun i j => raw27755step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27755step1 raw27755step0; decide +kernel
      have hl : raw27755step1Labels = raw27755step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27755step0 raw27755step0Labels permutation34 permutation2
    _ = mixedMoment B node1336 node1336Labels := by rfl

def raw27756 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw27756Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27756step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 2, 1]]
def raw27756step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27756step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw27756step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27756 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27756 raw27756Labels = mixedMoment B node1973 node1973Labels := by
  calc
    mixedMoment B raw27756 raw27756Labels = mixedMoment B raw27756step0 raw27756step0Labels := by
      have ha : raw27756step0 = (fun i j => raw27756 (permutation646 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27756step0 raw27756; decide +kernel
      have hl : raw27756step0Labels = raw27756Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27756 raw27756Labels permutation646 permutation2
    mixedMoment B raw27756step0 raw27756step0Labels = mixedMoment B raw27756step1 raw27756step1Labels := by
      have ha : raw27756step1 = -raw27756step0 := by apply Matrix.ext; change ∀ i j, raw27756step1 i j = -(raw27756step0 i j); unfold raw27756step1 raw27756step0; decide +kernel
      have hl : raw27756step1Labels = raw27756step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1973 node1973Labels := by rfl

def raw27757 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw27757Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27757step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw27757step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27757step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw27757step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27757step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27757step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27757 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27757 raw27757Labels = mixedMoment B node2025 node2025Labels := by
  calc
    mixedMoment B raw27757 raw27757Labels = mixedMoment B raw27757step0 raw27757step0Labels := by
      have hz : ∀ j, raw27757 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27757step0 = (fun i j => raw27757 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27757step0 raw27757; decide +kernel
      have hl : raw27757step0Labels = raw27757Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27757 raw27757Labels permutation434 hz
    mixedMoment B raw27757step0 raw27757step0Labels = mixedMoment B raw27757step1 raw27757step1Labels := by
      have ha : raw27757step1 = (fun i j => raw27757step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27757step1 raw27757step0; decide +kernel
      have hl : raw27757step1Labels = raw27757step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27757step0 raw27757step0Labels permutation145 permutation2
    mixedMoment B raw27757step1 raw27757step1Labels = mixedMoment B raw27757step2 raw27757step2Labels := by
      have ha : raw27757step2 = -raw27757step1 := by apply Matrix.ext; change ∀ i j, raw27757step2 i j = -(raw27757step1 i j); unfold raw27757step2 raw27757step1; decide +kernel
      have hl : raw27757step2Labels = raw27757step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2025 node2025Labels := by rfl

def raw27758 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw27758Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27758step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw27758step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27758step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw27758step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27758 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27758 raw27758Labels = mixedMoment B node2952 node2952Labels := by
  calc
    mixedMoment B raw27758 raw27758Labels = mixedMoment B raw27758step0 raw27758step0Labels := by
      have hz : ∀ j, raw27758 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27758step0 = (fun i j => raw27758 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27758step0 raw27758; decide +kernel
      have hl : raw27758step0Labels = raw27758Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27758 raw27758Labels permutation434 hz
    mixedMoment B raw27758step0 raw27758step0Labels = mixedMoment B raw27758step1 raw27758step1Labels := by
      have ha : raw27758step1 = (fun i j => raw27758step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27758step1 raw27758step0; decide +kernel
      have hl : raw27758step1Labels = raw27758step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27758step0 raw27758step0Labels permutation34 permutation2
    _ = mixedMoment B node2952 node2952Labels := by rfl

def raw27759 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw27759Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27759step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw27759step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27759step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![1, -2, 1], ![-3, 0, 3]]
def raw27759step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27759step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw27759step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw27759step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![3, -1, -2]]
def raw27759step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw27759step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![3, -1, -2]]
def raw27759step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27759 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27759 raw27759Labels = mixedMoment B node4868 node4868Labels := by
  calc
    mixedMoment B raw27759 raw27759Labels = mixedMoment B raw27759step0 raw27759step0Labels := by
      have hz : ∀ j, raw27759 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27759step0 = (fun i j => raw27759 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27759step0 raw27759; decide +kernel
      have hl : raw27759step0Labels = raw27759Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27759 raw27759Labels permutation434 hz
    mixedMoment B raw27759step0 raw27759step0Labels = mixedMoment B raw27759step1 raw27759step1Labels := by
      have hz : ∀ j, raw27759step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27759step1 = (fun i j => raw27759step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27759step1 raw27759step0; decide +kernel
      have hl : raw27759step1Labels = raw27759step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27759step0 raw27759step0Labels permutation80 hz
    mixedMoment B raw27759step1 raw27759step1Labels = mixedMoment B raw27759step2 raw27759step2Labels := by
      have ha : raw27759step2 = (fun i j => raw27759step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27759step2 raw27759step1; decide +kernel
      have hl : raw27759step2Labels = raw27759step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27759step1 raw27759step1Labels permutation31 permutation7
    mixedMoment B raw27759step2 raw27759step2Labels = mixedMoment B raw27759step3 raw27759step3Labels := by
      have ha : raw27759step3 = -raw27759step2 := by apply Matrix.ext; change ∀ i j, raw27759step3 i j = -(raw27759step2 i j); unfold raw27759step3 raw27759step2; decide +kernel
      have hl : raw27759step3Labels = raw27759step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27759step3 raw27759step3Labels = mixedMoment B raw27759step4 raw27759step4Labels := by
      have ha : raw27759step4 = raw27759step3 := by apply Matrix.ext; unfold raw27759step4 raw27759step3; decide +kernel
      have hl : raw27759step3Labels = labelEmbedding10 ∘ raw27759step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27759step3 raw27759step3Labels raw27759step4Labels labelEmbedding10 hl
    _ = mixedMoment B node4868 node4868Labels := by rfl

def raw27760 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw27760Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27760step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 1, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw27760step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27760step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw27760step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27760 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27760 raw27760Labels = mixedMoment B node4827 node4827Labels := by
  calc
    mixedMoment B raw27760 raw27760Labels = mixedMoment B raw27760step0 raw27760step0Labels := by
      have hz : ∀ j, raw27760 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27760step0 = (fun i j => raw27760 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27760step0 raw27760; decide +kernel
      have hl : raw27760step0Labels = raw27760Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27760 raw27760Labels permutation434 hz
    mixedMoment B raw27760step0 raw27760step0Labels = mixedMoment B raw27760step1 raw27760step1Labels := by
      have ha : raw27760step1 = (fun i j => raw27760step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27760step1 raw27760step0; decide +kernel
      have hl : raw27760step1Labels = raw27760step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27760step0 raw27760step0Labels permutation145 permutation2
    _ = mixedMoment B node4827 node4827Labels := by rfl

def raw27761 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw27761Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27761step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 1, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw27761step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27761step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw27761step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27761 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27761 raw27761Labels = mixedMoment B node4827 node4827Labels := by
  calc
    mixedMoment B raw27761 raw27761Labels = mixedMoment B raw27761step0 raw27761step0Labels := by
      have hz : ∀ j, raw27761 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27761step0 = (fun i j => raw27761 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27761step0 raw27761; decide +kernel
      have hl : raw27761step0Labels = raw27761Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27761 raw27761Labels permutation346 hz
    mixedMoment B raw27761step0 raw27761step0Labels = mixedMoment B raw27761step1 raw27761step1Labels := by
      have ha : raw27761step1 = (fun i j => raw27761step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27761step1 raw27761step0; decide +kernel
      have hl : raw27761step1Labels = raw27761step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27761step0 raw27761step0Labels permutation145 permutation2
    _ = mixedMoment B node4827 node4827Labels := by rfl

def raw27762 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-4, 1, 3]]
def raw27762Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27762step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 0, 0], ![1, -2, 1], ![-4, 1, 3]]
def raw27762step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27762step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![1, -2, 1], ![-4, 1, 3]]
def raw27762step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27762step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw27762step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27762 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27762 raw27762Labels = mixedMoment B node4490 node4490Labels := by
  calc
    mixedMoment B raw27762 raw27762Labels = mixedMoment B raw27762step0 raw27762step0Labels := by
      have hz : ∀ j, raw27762 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27762step0 = (fun i j => raw27762 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27762step0 raw27762; decide +kernel
      have hl : raw27762step0Labels = raw27762Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27762 raw27762Labels permutation434 hz
    mixedMoment B raw27762step0 raw27762step0Labels = mixedMoment B raw27762step1 raw27762step1Labels := by
      have hz : ∀ j, raw27762step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27762step1 = (fun i j => raw27762step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27762step1 raw27762step0; decide +kernel
      have hl : raw27762step1Labels = raw27762step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27762step0 raw27762step0Labels permutation80 hz
    mixedMoment B raw27762step1 raw27762step1Labels = mixedMoment B raw27762step2 raw27762step2Labels := by
      have ha : raw27762step2 = (fun i j => raw27762step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27762step2 raw27762step1; decide +kernel
      have hl : raw27762step2Labels = raw27762step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27762step1 raw27762step1Labels permutation31 permutation2
    _ = mixedMoment B node4490 node4490Labels := by rfl

def raw27763 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw27763Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27763step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw27763step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27763step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![1, -2, 1], ![-3, 0, 3]]
def raw27763step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27763step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 1, -2], ![3, -3, 0]]
def raw27763step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw27763step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 1, -2], ![3, -3, 0]]
def raw27763step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27763 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27763 raw27763Labels = mixedMoment B node4872 node4872Labels := by
  calc
    mixedMoment B raw27763 raw27763Labels = mixedMoment B raw27763step0 raw27763step0Labels := by
      have hz : ∀ j, raw27763 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27763step0 = (fun i j => raw27763 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27763step0 raw27763; decide +kernel
      have hl : raw27763step0Labels = raw27763Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27763 raw27763Labels permutation434 hz
    mixedMoment B raw27763step0 raw27763step0Labels = mixedMoment B raw27763step1 raw27763step1Labels := by
      have hz : ∀ j, raw27763step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27763step1 = (fun i j => raw27763step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27763step1 raw27763step0; decide +kernel
      have hl : raw27763step1Labels = raw27763step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27763step0 raw27763step0Labels permutation80 hz
    mixedMoment B raw27763step1 raw27763step1Labels = mixedMoment B raw27763step2 raw27763step2Labels := by
      have ha : raw27763step2 = (fun i j => raw27763step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw27763step2 raw27763step1; decide +kernel
      have hl : raw27763step2Labels = raw27763step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27763step1 raw27763step1Labels permutation8 permutation6
    mixedMoment B raw27763step2 raw27763step2Labels = mixedMoment B raw27763step3 raw27763step3Labels := by
      have ha : raw27763step3 = raw27763step2 := by apply Matrix.ext; unfold raw27763step3 raw27763step2; decide +kernel
      have hl : raw27763step2Labels = labelEmbedding9 ∘ raw27763step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27763step2 raw27763step2Labels raw27763step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4872 node4872Labels := by rfl

def raw27764 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw27764Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27764step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-1, 1, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw27764step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27764step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 2, -3], ![2, -1, -1]]
def raw27764step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27764 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27764 raw27764Labels = mixedMoment B node4829 node4829Labels := by
  calc
    mixedMoment B raw27764 raw27764Labels = mixedMoment B raw27764step0 raw27764step0Labels := by
      have hz : ∀ j, raw27764 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27764step0 = (fun i j => raw27764 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27764step0 raw27764; decide +kernel
      have hl : raw27764step0Labels = raw27764Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27764 raw27764Labels permutation434 hz
    mixedMoment B raw27764step0 raw27764step0Labels = mixedMoment B raw27764step1 raw27764step1Labels := by
      have ha : raw27764step1 = (fun i j => raw27764step0 (permutation144 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27764step1 raw27764step0; decide +kernel
      have hl : raw27764step1Labels = raw27764step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27764step0 raw27764step0Labels permutation144 permutation2
    _ = mixedMoment B node4829 node4829Labels := by rfl

def raw27765 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw27765Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27765step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-1, 1, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw27765step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27765step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 2, -3], ![2, -1, -1]]
def raw27765step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27765 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27765 raw27765Labels = mixedMoment B node4829 node4829Labels := by
  calc
    mixedMoment B raw27765 raw27765Labels = mixedMoment B raw27765step0 raw27765step0Labels := by
      have hz : ∀ j, raw27765 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27765step0 = (fun i j => raw27765 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27765step0 raw27765; decide +kernel
      have hl : raw27765step0Labels = raw27765Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27765 raw27765Labels permutation346 hz
    mixedMoment B raw27765step0 raw27765step0Labels = mixedMoment B raw27765step1 raw27765step1Labels := by
      have ha : raw27765step1 = (fun i j => raw27765step0 (permutation144 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27765step1 raw27765step0; decide +kernel
      have hl : raw27765step1Labels = raw27765step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27765step0 raw27765step0Labels permutation144 permutation2
    _ = mixedMoment B node4829 node4829Labels := by rfl

def raw27766 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-4, 1, 3]]
def raw27766Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27766step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![1, -2, 1], ![-4, 1, 3]]
def raw27766step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27766step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![1, -2, 1], ![-4, 1, 3]]
def raw27766step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27766step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 2, -3], ![2, -1, -1]]
def raw27766step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27766 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27766 raw27766Labels = mixedMoment B node4492 node4492Labels := by
  calc
    mixedMoment B raw27766 raw27766Labels = mixedMoment B raw27766step0 raw27766step0Labels := by
      have hz : ∀ j, raw27766 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27766step0 = (fun i j => raw27766 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27766step0 raw27766; decide +kernel
      have hl : raw27766step0Labels = raw27766Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27766 raw27766Labels permutation434 hz
    mixedMoment B raw27766step0 raw27766step0Labels = mixedMoment B raw27766step1 raw27766step1Labels := by
      have hz : ∀ j, raw27766step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27766step1 = (fun i j => raw27766step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27766step1 raw27766step0; decide +kernel
      have hl : raw27766step1Labels = raw27766step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27766step0 raw27766step0Labels permutation80 hz
    mixedMoment B raw27766step1 raw27766step1Labels = mixedMoment B raw27766step2 raw27766step2Labels := by
      have ha : raw27766step2 = (fun i j => raw27766step1 (permutation30 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27766step2 raw27766step1; decide +kernel
      have hl : raw27766step2Labels = raw27766step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27766step1 raw27766step1Labels permutation30 permutation2
    _ = mixedMoment B node4492 node4492Labels := by rfl

def raw27767 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw27767Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27767step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw27767step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27767step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw27767step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw27767step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw27767step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27767 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27767 raw27767Labels = mixedMoment B node4808 node4808Labels := by
  calc
    mixedMoment B raw27767 raw27767Labels = mixedMoment B raw27767step0 raw27767step0Labels := by
      have hz : ∀ j, raw27767 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27767step0 = (fun i j => raw27767 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27767step0 raw27767; decide +kernel
      have hl : raw27767step0Labels = raw27767Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27767 raw27767Labels permutation434 hz
    mixedMoment B raw27767step0 raw27767step0Labels = mixedMoment B raw27767step1 raw27767step1Labels := by
      have ha : raw27767step1 = (fun i j => raw27767step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw27767step1 raw27767step0; decide +kernel
      have hl : raw27767step1Labels = raw27767step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27767step0 raw27767step0Labels permutation32 permutation6
    mixedMoment B raw27767step1 raw27767step1Labels = mixedMoment B raw27767step2 raw27767step2Labels := by
      have ha : raw27767step2 = raw27767step1 := by apply Matrix.ext; unfold raw27767step2 raw27767step1; decide +kernel
      have hl : raw27767step1Labels = labelEmbedding9 ∘ raw27767step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27767step1 raw27767step1Labels raw27767step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4808 node4808Labels := by rfl

def raw27768 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw27768Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27768step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw27768step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27768step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 2, 1]]
def raw27768step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw27768step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw27768step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw27768step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw27768step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27768 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27768 raw27768Labels = mixedMoment B node4853 node4853Labels := by
  calc
    mixedMoment B raw27768 raw27768Labels = mixedMoment B raw27768step0 raw27768step0Labels := by
      have hz : ∀ j, raw27768 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27768step0 = (fun i j => raw27768 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27768step0 raw27768; decide +kernel
      have hl : raw27768step0Labels = raw27768Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27768 raw27768Labels permutation434 hz
    mixedMoment B raw27768step0 raw27768step0Labels = mixedMoment B raw27768step1 raw27768step1Labels := by
      have ha : raw27768step1 = (fun i j => raw27768step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27768step1 raw27768step0; decide +kernel
      have hl : raw27768step1Labels = raw27768step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27768step0 raw27768step0Labels permutation151 permutation7
    mixedMoment B raw27768step1 raw27768step1Labels = mixedMoment B raw27768step2 raw27768step2Labels := by
      have ha : raw27768step2 = -raw27768step1 := by apply Matrix.ext; change ∀ i j, raw27768step2 i j = -(raw27768step1 i j); unfold raw27768step2 raw27768step1; decide +kernel
      have hl : raw27768step2Labels = raw27768step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27768step2 raw27768step2Labels = mixedMoment B raw27768step3 raw27768step3Labels := by
      have ha : raw27768step3 = raw27768step2 := by apply Matrix.ext; unfold raw27768step3 raw27768step2; decide +kernel
      have hl : raw27768step2Labels = labelEmbedding10 ∘ raw27768step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27768step2 raw27768step2Labels raw27768step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4853 node4853Labels := by rfl

def raw27769 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw27769Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27769step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw27769step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27769 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27769 raw27769Labels = mixedMoment B node4824 node4824Labels := by
  calc
    mixedMoment B raw27769 raw27769Labels = mixedMoment B raw27769step0 raw27769step0Labels := by
      have ha : raw27769step0 = (fun i j => raw27769 (permutation664 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27769step0 raw27769; decide +kernel
      have hl : raw27769step0Labels = raw27769Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27769 raw27769Labels permutation664 permutation2
    _ = mixedMoment B node4824 node4824Labels := by rfl

def raw27770 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![-4, 1, 3]]
def raw27770Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27770step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1], ![-4, 1, 3]]
def raw27770step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27770step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw27770step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27770 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27770 raw27770Labels = mixedMoment B node4486 node4486Labels := by
  calc
    mixedMoment B raw27770 raw27770Labels = mixedMoment B raw27770step0 raw27770step0Labels := by
      have hz : ∀ j, raw27770 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27770step0 = (fun i j => raw27770 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27770step0 raw27770; decide +kernel
      have hl : raw27770step0Labels = raw27770Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27770 raw27770Labels permutation434 hz
    mixedMoment B raw27770step0 raw27770step0Labels = mixedMoment B raw27770step1 raw27770step1Labels := by
      have ha : raw27770step1 = (fun i j => raw27770step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27770step1 raw27770step0; decide +kernel
      have hl : raw27770step1Labels = raw27770step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27770step0 raw27770step0Labels permutation151 permutation2
    _ = mixedMoment B node4486 node4486Labels := by rfl

def raw27771 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw27771Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27771step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw27771step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27771step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw27771step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw27771step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw27771step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27771 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27771 raw27771Labels = mixedMoment B node4808 node4808Labels := by
  calc
    mixedMoment B raw27771 raw27771Labels = mixedMoment B raw27771step0 raw27771step0Labels := by
      have hz : ∀ j, raw27771 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27771step0 = (fun i j => raw27771 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27771step0 raw27771; decide +kernel
      have hl : raw27771step0Labels = raw27771Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27771 raw27771Labels permutation346 hz
    mixedMoment B raw27771step0 raw27771step0Labels = mixedMoment B raw27771step1 raw27771step1Labels := by
      have ha : raw27771step1 = (fun i j => raw27771step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw27771step1 raw27771step0; decide +kernel
      have hl : raw27771step1Labels = raw27771step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27771step0 raw27771step0Labels permutation32 permutation6
    mixedMoment B raw27771step1 raw27771step1Labels = mixedMoment B raw27771step2 raw27771step2Labels := by
      have ha : raw27771step2 = raw27771step1 := by apply Matrix.ext; unfold raw27771step2 raw27771step1; decide +kernel
      have hl : raw27771step1Labels = labelEmbedding9 ∘ raw27771step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27771step1 raw27771step1Labels raw27771step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4808 node4808Labels := by rfl

def raw27772 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw27772Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27772step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw27772step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27772step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 2, 1]]
def raw27772step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw27772step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw27772step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw27772step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw27772step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27772 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27772 raw27772Labels = mixedMoment B node4853 node4853Labels := by
  calc
    mixedMoment B raw27772 raw27772Labels = mixedMoment B raw27772step0 raw27772step0Labels := by
      have hz : ∀ j, raw27772 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27772step0 = (fun i j => raw27772 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27772step0 raw27772; decide +kernel
      have hl : raw27772step0Labels = raw27772Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27772 raw27772Labels permutation346 hz
    mixedMoment B raw27772step0 raw27772step0Labels = mixedMoment B raw27772step1 raw27772step1Labels := by
      have ha : raw27772step1 = (fun i j => raw27772step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27772step1 raw27772step0; decide +kernel
      have hl : raw27772step1Labels = raw27772step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27772step0 raw27772step0Labels permutation151 permutation7
    mixedMoment B raw27772step1 raw27772step1Labels = mixedMoment B raw27772step2 raw27772step2Labels := by
      have ha : raw27772step2 = -raw27772step1 := by apply Matrix.ext; change ∀ i j, raw27772step2 i j = -(raw27772step1 i j); unfold raw27772step2 raw27772step1; decide +kernel
      have hl : raw27772step2Labels = raw27772step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27772step2 raw27772step2Labels = mixedMoment B raw27772step3 raw27772step3Labels := by
      have ha : raw27772step3 = raw27772step2 := by apply Matrix.ext; unfold raw27772step3 raw27772step2; decide +kernel
      have hl : raw27772step2Labels = labelEmbedding10 ∘ raw27772step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27772step2 raw27772step2Labels raw27772step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4853 node4853Labels := by rfl

def raw27773 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw27773Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27773step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw27773step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27773 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27773 raw27773Labels = mixedMoment B node4824 node4824Labels := by
  calc
    mixedMoment B raw27773 raw27773Labels = mixedMoment B raw27773step0 raw27773step0Labels := by
      have ha : raw27773step0 = (fun i j => raw27773 (permutation646 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27773step0 raw27773; decide +kernel
      have hl : raw27773step0Labels = raw27773Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27773 raw27773Labels permutation646 permutation2
    _ = mixedMoment B node4824 node4824Labels := by rfl

def raw27774 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-4, 1, 3]]
def raw27774Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27774step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1], ![-4, 1, 3]]
def raw27774step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27774step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw27774step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27774 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27774 raw27774Labels = mixedMoment B node4486 node4486Labels := by
  calc
    mixedMoment B raw27774 raw27774Labels = mixedMoment B raw27774step0 raw27774step0Labels := by
      have hz : ∀ j, raw27774 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27774step0 = (fun i j => raw27774 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27774step0 raw27774; decide +kernel
      have hl : raw27774step0Labels = raw27774Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27774 raw27774Labels permutation346 hz
    mixedMoment B raw27774step0 raw27774step0Labels = mixedMoment B raw27774step1 raw27774step1Labels := by
      have ha : raw27774step1 = (fun i j => raw27774step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27774step1 raw27774step0; decide +kernel
      have hl : raw27774step1Labels = raw27774step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27774step0 raw27774step0Labels permutation151 permutation2
    _ = mixedMoment B node4486 node4486Labels := by rfl

def raw27775 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![-3, 0, 3]]
def raw27775Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27775step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![2, -3, 1], ![-3, 0, 3]]
def raw27775step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27775step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![2, -3, 1], ![-3, 0, 3]]
def raw27775step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27775step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 2, -3], ![3, -3, 0]]
def raw27775step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw27775step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 2, -3], ![3, -3, 0]]
def raw27775step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27775 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27775 raw27775Labels = mixedMoment B node4844 node4844Labels := by
  calc
    mixedMoment B raw27775 raw27775Labels = mixedMoment B raw27775step0 raw27775step0Labels := by
      have hz : ∀ j, raw27775 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27775step0 = (fun i j => raw27775 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27775step0 raw27775; decide +kernel
      have hl : raw27775step0Labels = raw27775Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27775 raw27775Labels permutation434 hz
    mixedMoment B raw27775step0 raw27775step0Labels = mixedMoment B raw27775step1 raw27775step1Labels := by
      have hz : ∀ j, raw27775step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27775step1 = (fun i j => raw27775step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27775step1 raw27775step0; decide +kernel
      have hl : raw27775step1Labels = raw27775step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27775step0 raw27775step0Labels permutation80 hz
    mixedMoment B raw27775step1 raw27775step1Labels = mixedMoment B raw27775step2 raw27775step2Labels := by
      have ha : raw27775step2 = (fun i j => raw27775step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw27775step2 raw27775step1; decide +kernel
      have hl : raw27775step2Labels = raw27775step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27775step1 raw27775step1Labels permutation8 permutation6
    mixedMoment B raw27775step2 raw27775step2Labels = mixedMoment B raw27775step3 raw27775step3Labels := by
      have ha : raw27775step3 = raw27775step2 := by apply Matrix.ext; unfold raw27775step3 raw27775step2; decide +kernel
      have hl : raw27775step2Labels = labelEmbedding9 ∘ raw27775step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27775step2 raw27775step2Labels raw27775step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4844 node4844Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
