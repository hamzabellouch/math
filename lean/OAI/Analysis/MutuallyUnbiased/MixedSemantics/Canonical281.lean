import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes73
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes74
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes78
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw35968 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35968Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35968step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35968step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35968step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw35968step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35968step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw35968step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35968step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw35968step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35968 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35968 raw35968Labels = mixedMoment B node5236 node5236Labels := by
  calc
    mixedMoment B raw35968 raw35968Labels = mixedMoment B raw35968step0 raw35968step0Labels := by
      have hz : ∀ j, raw35968 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35968step0 = (fun i j => raw35968 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35968step0 raw35968; decide +kernel
      have hl : raw35968step0Labels = raw35968Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35968 raw35968Labels permutation346 hz
    mixedMoment B raw35968step0 raw35968step0Labels = mixedMoment B raw35968step1 raw35968step1Labels := by
      have ha : raw35968step1 = (fun i j => raw35968step0 (permutation56 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35968step1 raw35968step0; decide +kernel
      have hl : raw35968step1Labels = raw35968step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35968step0 raw35968step0Labels permutation56 permutation7
    mixedMoment B raw35968step1 raw35968step1Labels = mixedMoment B raw35968step2 raw35968step2Labels := by
      have ha : raw35968step2 = -raw35968step1 := by apply Matrix.ext; change ∀ i j, raw35968step2 i j = -(raw35968step1 i j); unfold raw35968step2 raw35968step1; decide +kernel
      have hl : raw35968step2Labels = raw35968step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35968step2 raw35968step2Labels = mixedMoment B raw35968step3 raw35968step3Labels := by
      have ha : raw35968step3 = raw35968step2 := by apply Matrix.ext; unfold raw35968step3 raw35968step2; decide +kernel
      have hl : raw35968step2Labels = labelEmbedding10 ∘ raw35968step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35968step2 raw35968step2Labels raw35968step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5236 node5236Labels := by rfl

def raw35969 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw35969Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35969step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw35969step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35969step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw35969step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35969step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw35969step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35969step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw35969step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35969 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35969 raw35969Labels = mixedMoment B node5237 node5237Labels := by
  calc
    mixedMoment B raw35969 raw35969Labels = mixedMoment B raw35969step0 raw35969step0Labels := by
      have hz : ∀ j, raw35969 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35969step0 = (fun i j => raw35969 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35969step0 raw35969; decide +kernel
      have hl : raw35969step0Labels = raw35969Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35969 raw35969Labels permutation346 hz
    mixedMoment B raw35969step0 raw35969step0Labels = mixedMoment B raw35969step1 raw35969step1Labels := by
      have ha : raw35969step1 = (fun i j => raw35969step0 (permutation57 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35969step1 raw35969step0; decide +kernel
      have hl : raw35969step1Labels = raw35969step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35969step0 raw35969step0Labels permutation57 permutation7
    mixedMoment B raw35969step1 raw35969step1Labels = mixedMoment B raw35969step2 raw35969step2Labels := by
      have ha : raw35969step2 = -raw35969step1 := by apply Matrix.ext; change ∀ i j, raw35969step2 i j = -(raw35969step1 i j); unfold raw35969step2 raw35969step1; decide +kernel
      have hl : raw35969step2Labels = raw35969step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35969step2 raw35969step2Labels = mixedMoment B raw35969step3 raw35969step3Labels := by
      have ha : raw35969step3 = raw35969step2 := by apply Matrix.ext; unfold raw35969step3 raw35969step2; decide +kernel
      have hl : raw35969step2Labels = labelEmbedding10 ∘ raw35969step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35969step2 raw35969step2Labels raw35969step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5237 node5237Labels := by rfl

def raw35970 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw35970Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35970step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw35970step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35970step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw35970step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35970step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw35970step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35970 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35970 raw35970Labels = mixedMoment B node4697 node4697Labels := by
  calc
    mixedMoment B raw35970 raw35970Labels = mixedMoment B raw35970step0 raw35970step0Labels := by
      have hz : ∀ j, raw35970 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35970step0 = (fun i j => raw35970 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35970step0 raw35970; decide +kernel
      have hl : raw35970step0Labels = raw35970Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35970 raw35970Labels permutation346 hz
    mixedMoment B raw35970step0 raw35970step0Labels = mixedMoment B raw35970step1 raw35970step1Labels := by
      have ha : raw35970step1 = (fun i j => raw35970step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35970step1 raw35970step0; decide +kernel
      have hl : raw35970step1Labels = raw35970step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35970step0 raw35970step0Labels permutation32 permutation3
    mixedMoment B raw35970step1 raw35970step1Labels = mixedMoment B raw35970step2 raw35970step2Labels := by
      have ha : raw35970step2 = raw35970step1 := by apply Matrix.ext; unfold raw35970step2 raw35970step1; decide +kernel
      have hl : raw35970step1Labels = labelEmbedding6 ∘ raw35970step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35970step1 raw35970step1Labels raw35970step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4697 node4697Labels := by rfl

def raw35971 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 0, 3], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw35971Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35971step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 0, 3], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw35971step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35971step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw35971step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35971 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35971 raw35971Labels = mixedMoment B node4686 node4686Labels := by
  calc
    mixedMoment B raw35971 raw35971Labels = mixedMoment B raw35971step0 raw35971step0Labels := by
      have hz : ∀ j, raw35971 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35971step0 = (fun i j => raw35971 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35971step0 raw35971; decide +kernel
      have hl : raw35971step0Labels = raw35971Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35971 raw35971Labels permutation346 hz
    mixedMoment B raw35971step0 raw35971step0Labels = mixedMoment B raw35971step1 raw35971step1Labels := by
      have ha : raw35971step1 = (fun i j => raw35971step0 (permutation56 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35971step1 raw35971step0; decide +kernel
      have hl : raw35971step1Labels = raw35971step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35971step0 raw35971step0Labels permutation56 permutation2
    _ = mixedMoment B node4686 node4686Labels := by rfl

def raw35972 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw35972Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35972step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 3, -1], ![-2, 0, 2]]
def raw35972step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35972step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw35972step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35972step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw35972step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35972 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35972 raw35972Labels = mixedMoment B node5116 node5116Labels := by
  calc
    mixedMoment B raw35972 raw35972Labels = mixedMoment B raw35972step0 raw35972step0Labels := by
      have ha : raw35972step0 = (fun i j => raw35972 (permutation664 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35972step0 raw35972; decide +kernel
      have hl : raw35972step0Labels = raw35972Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35972 raw35972Labels permutation664 permutation3
    mixedMoment B raw35972step0 raw35972step0Labels = mixedMoment B raw35972step1 raw35972step1Labels := by
      have ha : raw35972step1 = -raw35972step0 := by apply Matrix.ext; change ∀ i j, raw35972step1 i j = -(raw35972step0 i j); unfold raw35972step1 raw35972step0; decide +kernel
      have hl : raw35972step1Labels = raw35972step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35972step1 raw35972step1Labels = mixedMoment B raw35972step2 raw35972step2Labels := by
      have ha : raw35972step2 = raw35972step1 := by apply Matrix.ext; unfold raw35972step2 raw35972step1; decide +kernel
      have hl : raw35972step1Labels = labelEmbedding6 ∘ raw35972step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35972step1 raw35972step1Labels raw35972step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5116 node5116Labels := by rfl

def raw35973 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw35973Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35973step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw35973step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35973step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, -1, 1], ![-2, 3, -1], ![-2, 0, 2]]
def raw35973step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35973step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw35973step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35973step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw35973step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35973 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35973 raw35973Labels = mixedMoment B node5151 node5151Labels := by
  calc
    mixedMoment B raw35973 raw35973Labels = mixedMoment B raw35973step0 raw35973step0Labels := by
      have hz : ∀ j, raw35973 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35973step0 = (fun i j => raw35973 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35973step0 raw35973; decide +kernel
      have hl : raw35973step0Labels = raw35973Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35973 raw35973Labels permutation346 hz
    mixedMoment B raw35973step0 raw35973step0Labels = mixedMoment B raw35973step1 raw35973step1Labels := by
      have ha : raw35973step1 = (fun i j => raw35973step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35973step1 raw35973step0; decide +kernel
      have hl : raw35973step1Labels = raw35973step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35973step0 raw35973step0Labels permutation151 permutation3
    mixedMoment B raw35973step1 raw35973step1Labels = mixedMoment B raw35973step2 raw35973step2Labels := by
      have ha : raw35973step2 = -raw35973step1 := by apply Matrix.ext; change ∀ i j, raw35973step2 i j = -(raw35973step1 i j); unfold raw35973step2 raw35973step1; decide +kernel
      have hl : raw35973step2Labels = raw35973step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35973step2 raw35973step2Labels = mixedMoment B raw35973step3 raw35973step3Labels := by
      have ha : raw35973step3 = raw35973step2 := by apply Matrix.ext; unfold raw35973step3 raw35973step2; decide +kernel
      have hl : raw35973step2Labels = labelEmbedding6 ∘ raw35973step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35973step2 raw35973step2Labels raw35973step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5151 node5151Labels := by rfl

def raw35974 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![3, -2, -1]]
def raw35974Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35974step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![1, 0, -1], ![0, 1, -1], ![3, -2, -1]]
def raw35974step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35974step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, -1, 1], ![-2, 3, -1], ![-2, 0, 2]]
def raw35974step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35974step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw35974step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35974step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw35974step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35974 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35974 raw35974Labels = mixedMoment B node5151 node5151Labels := by
  calc
    mixedMoment B raw35974 raw35974Labels = mixedMoment B raw35974step0 raw35974step0Labels := by
      have hz : ∀ j, raw35974 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35974step0 = (fun i j => raw35974 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35974step0 raw35974; decide +kernel
      have hl : raw35974step0Labels = raw35974Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35974 raw35974Labels permutation346 hz
    mixedMoment B raw35974step0 raw35974step0Labels = mixedMoment B raw35974step1 raw35974step1Labels := by
      have ha : raw35974step1 = (fun i j => raw35974step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35974step1 raw35974step0; decide +kernel
      have hl : raw35974step1Labels = raw35974step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35974step0 raw35974step0Labels permutation145 permutation3
    mixedMoment B raw35974step1 raw35974step1Labels = mixedMoment B raw35974step2 raw35974step2Labels := by
      have ha : raw35974step2 = -raw35974step1 := by apply Matrix.ext; change ∀ i j, raw35974step2 i j = -(raw35974step1 i j); unfold raw35974step2 raw35974step1; decide +kernel
      have hl : raw35974step2Labels = raw35974step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35974step2 raw35974step2Labels = mixedMoment B raw35974step3 raw35974step3Labels := by
      have ha : raw35974step3 = raw35974step2 := by apply Matrix.ext; unfold raw35974step3 raw35974step2; decide +kernel
      have hl : raw35974step2Labels = labelEmbedding6 ∘ raw35974step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35974step2 raw35974step2Labels raw35974step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5151 node5151Labels := by rfl

def raw35975 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-3, 0, 3], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35975Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35975step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-3, 0, 3], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35975step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35975step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw35975step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35975step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw35975step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35975step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw35975step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35975 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35975 raw35975Labels = mixedMoment B node2227 node2227Labels := by
  calc
    mixedMoment B raw35975 raw35975Labels = mixedMoment B raw35975step0 raw35975step0Labels := by
      have hz : ∀ j, raw35975 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35975step0 = (fun i j => raw35975 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35975step0 raw35975; decide +kernel
      have hl : raw35975step0Labels = raw35975Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35975 raw35975Labels permutation346 hz
    mixedMoment B raw35975step0 raw35975step0Labels = mixedMoment B raw35975step1 raw35975step1Labels := by
      have ha : raw35975step1 = (fun i j => raw35975step0 (permutation56 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35975step1 raw35975step0; decide +kernel
      have hl : raw35975step1Labels = raw35975step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35975step0 raw35975step0Labels permutation56 permutation7
    mixedMoment B raw35975step1 raw35975step1Labels = mixedMoment B raw35975step2 raw35975step2Labels := by
      have ha : raw35975step2 = -raw35975step1 := by apply Matrix.ext; change ∀ i j, raw35975step2 i j = -(raw35975step1 i j); unfold raw35975step2 raw35975step1; decide +kernel
      have hl : raw35975step2Labels = raw35975step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35975step2 raw35975step2Labels = mixedMoment B raw35975step3 raw35975step3Labels := by
      have ha : raw35975step3 = raw35975step2 := by apply Matrix.ext; unfold raw35975step3 raw35975step2; decide +kernel
      have hl : raw35975step2Labels = labelEmbedding1 ∘ raw35975step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35975step2 raw35975step2Labels raw35975step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2227 node2227Labels := by rfl

def raw35976 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35976Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35976step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw35976step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35976step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw35976step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35976step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw35976step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35976 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35976 raw35976Labels = mixedMoment B node2703 node2703Labels := by
  calc
    mixedMoment B raw35976 raw35976Labels = mixedMoment B raw35976step0 raw35976step0Labels := by
      have ha : raw35976step0 = (fun i j => raw35976 (permutation265 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35976step0 raw35976; decide +kernel
      have hl : raw35976step0Labels = raw35976Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35976 raw35976Labels permutation265 permutation7
    mixedMoment B raw35976step0 raw35976step0Labels = mixedMoment B raw35976step1 raw35976step1Labels := by
      have ha : raw35976step1 = -raw35976step0 := by apply Matrix.ext; change ∀ i j, raw35976step1 i j = -(raw35976step0 i j); unfold raw35976step1 raw35976step0; decide +kernel
      have hl : raw35976step1Labels = raw35976step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35976step1 raw35976step1Labels = mixedMoment B raw35976step2 raw35976step2Labels := by
      have ha : raw35976step2 = raw35976step1 := by apply Matrix.ext; unfold raw35976step2 raw35976step1; decide +kernel
      have hl : raw35976step1Labels = labelEmbedding1 ∘ raw35976step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35976step1 raw35976step1Labels raw35976step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2703 node2703Labels := by rfl

def raw35977 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35977Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35977step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35977step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35977step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw35977step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35977step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw35977step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35977step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw35977step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35977 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35977 raw35977Labels = mixedMoment B node2739 node2739Labels := by
  calc
    mixedMoment B raw35977 raw35977Labels = mixedMoment B raw35977step0 raw35977step0Labels := by
      have hz : ∀ j, raw35977 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35977step0 = (fun i j => raw35977 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35977step0 raw35977; decide +kernel
      have hl : raw35977step0Labels = raw35977Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35977 raw35977Labels permutation346 hz
    mixedMoment B raw35977step0 raw35977step0Labels = mixedMoment B raw35977step1 raw35977step1Labels := by
      have ha : raw35977step1 = (fun i j => raw35977step0 (permutation56 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35977step1 raw35977step0; decide +kernel
      have hl : raw35977step1Labels = raw35977step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35977step0 raw35977step0Labels permutation56 permutation7
    mixedMoment B raw35977step1 raw35977step1Labels = mixedMoment B raw35977step2 raw35977step2Labels := by
      have ha : raw35977step2 = -raw35977step1 := by apply Matrix.ext; change ∀ i j, raw35977step2 i j = -(raw35977step1 i j); unfold raw35977step2 raw35977step1; decide +kernel
      have hl : raw35977step2Labels = raw35977step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35977step2 raw35977step2Labels = mixedMoment B raw35977step3 raw35977step3Labels := by
      have ha : raw35977step3 = raw35977step2 := by apply Matrix.ext; unfold raw35977step3 raw35977step2; decide +kernel
      have hl : raw35977step2Labels = labelEmbedding1 ∘ raw35977step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35977step2 raw35977step2Labels raw35977step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2739 node2739Labels := by rfl

def raw35978 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw35978Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35978step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw35978step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35978step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw35978step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35978step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw35978step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35978step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw35978step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35978 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35978 raw35978Labels = mixedMoment B node2739 node2739Labels := by
  calc
    mixedMoment B raw35978 raw35978Labels = mixedMoment B raw35978step0 raw35978step0Labels := by
      have hz : ∀ j, raw35978 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35978step0 = (fun i j => raw35978 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35978step0 raw35978; decide +kernel
      have hl : raw35978step0Labels = raw35978Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35978 raw35978Labels permutation346 hz
    mixedMoment B raw35978step0 raw35978step0Labels = mixedMoment B raw35978step1 raw35978step1Labels := by
      have ha : raw35978step1 = (fun i j => raw35978step0 (permutation58 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35978step1 raw35978step0; decide +kernel
      have hl : raw35978step1Labels = raw35978step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35978step0 raw35978step0Labels permutation58 permutation7
    mixedMoment B raw35978step1 raw35978step1Labels = mixedMoment B raw35978step2 raw35978step2Labels := by
      have ha : raw35978step2 = -raw35978step1 := by apply Matrix.ext; change ∀ i j, raw35978step2 i j = -(raw35978step1 i j); unfold raw35978step2 raw35978step1; decide +kernel
      have hl : raw35978step2Labels = raw35978step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35978step2 raw35978step2Labels = mixedMoment B raw35978step3 raw35978step3Labels := by
      have ha : raw35978step3 = raw35978step2 := by apply Matrix.ext; unfold raw35978step3 raw35978step2; decide +kernel
      have hl : raw35978step2Labels = labelEmbedding1 ∘ raw35978step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35978step2 raw35978step2Labels raw35978step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2739 node2739Labels := by rfl

def raw35979 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw35979Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35979step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw35979step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35979step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw35979step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35979step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw35979step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35979step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw35979step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35979 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35979 raw35979Labels = mixedMoment B node2741 node2741Labels := by
  calc
    mixedMoment B raw35979 raw35979Labels = mixedMoment B raw35979step0 raw35979step0Labels := by
      have hz : ∀ j, raw35979 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35979step0 = (fun i j => raw35979 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35979step0 raw35979; decide +kernel
      have hl : raw35979step0Labels = raw35979Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35979 raw35979Labels permutation346 hz
    mixedMoment B raw35979step0 raw35979step0Labels = mixedMoment B raw35979step1 raw35979step1Labels := by
      have ha : raw35979step1 = (fun i j => raw35979step0 (permutation56 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35979step1 raw35979step0; decide +kernel
      have hl : raw35979step1Labels = raw35979step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35979step0 raw35979step0Labels permutation56 permutation7
    mixedMoment B raw35979step1 raw35979step1Labels = mixedMoment B raw35979step2 raw35979step2Labels := by
      have ha : raw35979step2 = -raw35979step1 := by apply Matrix.ext; change ∀ i j, raw35979step2 i j = -(raw35979step1 i j); unfold raw35979step2 raw35979step1; decide +kernel
      have hl : raw35979step2Labels = raw35979step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35979step2 raw35979step2Labels = mixedMoment B raw35979step3 raw35979step3Labels := by
      have ha : raw35979step3 = raw35979step2 := by apply Matrix.ext; unfold raw35979step3 raw35979step2; decide +kernel
      have hl : raw35979step2Labels = labelEmbedding1 ∘ raw35979step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35979step2 raw35979step2Labels raw35979step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2741 node2741Labels := by rfl

def raw35980 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35980Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35980step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35980step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35980step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![-2, 3, -1]]
def raw35980step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35980step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw35980step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35980step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw35980step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35980 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35980 raw35980Labels = mixedMoment B node2246 node2246Labels := by
  calc
    mixedMoment B raw35980 raw35980Labels = mixedMoment B raw35980step0 raw35980step0Labels := by
      have hz : ∀ j, raw35980 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35980step0 = (fun i j => raw35980 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35980step0 raw35980; decide +kernel
      have hl : raw35980step0Labels = raw35980Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35980 raw35980Labels permutation346 hz
    mixedMoment B raw35980step0 raw35980step0Labels = mixedMoment B raw35980step1 raw35980step1Labels := by
      have ha : raw35980step1 = (fun i j => raw35980step0 (permutation41 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35980step1 raw35980step0; decide +kernel
      have hl : raw35980step1Labels = raw35980step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35980step0 raw35980step0Labels permutation41 permutation5
    mixedMoment B raw35980step1 raw35980step1Labels = mixedMoment B raw35980step2 raw35980step2Labels := by
      have ha : raw35980step2 = -raw35980step1 := by apply Matrix.ext; change ∀ i j, raw35980step2 i j = -(raw35980step1 i j); unfold raw35980step2 raw35980step1; decide +kernel
      have hl : raw35980step2Labels = raw35980step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35980step2 raw35980step2Labels = mixedMoment B raw35980step3 raw35980step3Labels := by
      have ha : raw35980step3 = raw35980step2 := by apply Matrix.ext; unfold raw35980step3 raw35980step2; decide +kernel
      have hl : raw35980step2Labels = labelEmbedding1 ∘ raw35980step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35980step2 raw35980step2Labels raw35980step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2246 node2246Labels := by rfl

def raw35981 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35981Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35981step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw35981step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35981step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw35981step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35981step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw35981step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35981 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35981 raw35981Labels = mixedMoment B node3023 node3023Labels := by
  calc
    mixedMoment B raw35981 raw35981Labels = mixedMoment B raw35981step0 raw35981step0Labels := by
      have ha : raw35981step0 = (fun i j => raw35981 (permutation265 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35981step0 raw35981; decide +kernel
      have hl : raw35981step0Labels = raw35981Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35981 raw35981Labels permutation265 permutation7
    mixedMoment B raw35981step0 raw35981step0Labels = mixedMoment B raw35981step1 raw35981step1Labels := by
      have ha : raw35981step1 = -raw35981step0 := by apply Matrix.ext; change ∀ i j, raw35981step1 i j = -(raw35981step0 i j); unfold raw35981step1 raw35981step0; decide +kernel
      have hl : raw35981step1Labels = raw35981step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35981step1 raw35981step1Labels = mixedMoment B raw35981step2 raw35981step2Labels := by
      have ha : raw35981step2 = raw35981step1 := by apply Matrix.ext; unfold raw35981step2 raw35981step1; decide +kernel
      have hl : raw35981step1Labels = labelEmbedding1 ∘ raw35981step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35981step1 raw35981step1Labels raw35981step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3023 node3023Labels := by rfl

def raw35982 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35982Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35982step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35982step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35982step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw35982step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35982step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw35982step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35982step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw35982step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35982 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35982 raw35982Labels = mixedMoment B node3051 node3051Labels := by
  calc
    mixedMoment B raw35982 raw35982Labels = mixedMoment B raw35982step0 raw35982step0Labels := by
      have hz : ∀ j, raw35982 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35982step0 = (fun i j => raw35982 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35982step0 raw35982; decide +kernel
      have hl : raw35982step0Labels = raw35982Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35982 raw35982Labels permutation346 hz
    mixedMoment B raw35982step0 raw35982step0Labels = mixedMoment B raw35982step1 raw35982step1Labels := by
      have ha : raw35982step1 = (fun i j => raw35982step0 (permutation56 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35982step1 raw35982step0; decide +kernel
      have hl : raw35982step1Labels = raw35982step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35982step0 raw35982step0Labels permutation56 permutation7
    mixedMoment B raw35982step1 raw35982step1Labels = mixedMoment B raw35982step2 raw35982step2Labels := by
      have ha : raw35982step2 = -raw35982step1 := by apply Matrix.ext; change ∀ i j, raw35982step2 i j = -(raw35982step1 i j); unfold raw35982step2 raw35982step1; decide +kernel
      have hl : raw35982step2Labels = raw35982step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35982step2 raw35982step2Labels = mixedMoment B raw35982step3 raw35982step3Labels := by
      have ha : raw35982step3 = raw35982step2 := by apply Matrix.ext; unfold raw35982step3 raw35982step2; decide +kernel
      have hl : raw35982step2Labels = labelEmbedding1 ∘ raw35982step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35982step2 raw35982step2Labels raw35982step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3051 node3051Labels := by rfl

def raw35983 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw35983Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35983step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw35983step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35983step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw35983step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35983step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw35983step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35983step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw35983step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35983 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35983 raw35983Labels = mixedMoment B node3051 node3051Labels := by
  calc
    mixedMoment B raw35983 raw35983Labels = mixedMoment B raw35983step0 raw35983step0Labels := by
      have hz : ∀ j, raw35983 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35983step0 = (fun i j => raw35983 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35983step0 raw35983; decide +kernel
      have hl : raw35983step0Labels = raw35983Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35983 raw35983Labels permutation346 hz
    mixedMoment B raw35983step0 raw35983step0Labels = mixedMoment B raw35983step1 raw35983step1Labels := by
      have ha : raw35983step1 = (fun i j => raw35983step0 (permutation58 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35983step1 raw35983step0; decide +kernel
      have hl : raw35983step1Labels = raw35983step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35983step0 raw35983step0Labels permutation58 permutation7
    mixedMoment B raw35983step1 raw35983step1Labels = mixedMoment B raw35983step2 raw35983step2Labels := by
      have ha : raw35983step2 = -raw35983step1 := by apply Matrix.ext; change ∀ i j, raw35983step2 i j = -(raw35983step1 i j); unfold raw35983step2 raw35983step1; decide +kernel
      have hl : raw35983step2Labels = raw35983step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35983step2 raw35983step2Labels = mixedMoment B raw35983step3 raw35983step3Labels := by
      have ha : raw35983step3 = raw35983step2 := by apply Matrix.ext; unfold raw35983step3 raw35983step2; decide +kernel
      have hl : raw35983step2Labels = labelEmbedding1 ∘ raw35983step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35983step2 raw35983step2Labels raw35983step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3051 node3051Labels := by rfl

def raw35984 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw35984Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35984step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw35984step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35984step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw35984step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35984step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw35984step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35984step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw35984step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35984 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35984 raw35984Labels = mixedMoment B node3053 node3053Labels := by
  calc
    mixedMoment B raw35984 raw35984Labels = mixedMoment B raw35984step0 raw35984step0Labels := by
      have hz : ∀ j, raw35984 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35984step0 = (fun i j => raw35984 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35984step0 raw35984; decide +kernel
      have hl : raw35984step0Labels = raw35984Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35984 raw35984Labels permutation346 hz
    mixedMoment B raw35984step0 raw35984step0Labels = mixedMoment B raw35984step1 raw35984step1Labels := by
      have ha : raw35984step1 = (fun i j => raw35984step0 (permutation56 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35984step1 raw35984step0; decide +kernel
      have hl : raw35984step1Labels = raw35984step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35984step0 raw35984step0Labels permutation56 permutation7
    mixedMoment B raw35984step1 raw35984step1Labels = mixedMoment B raw35984step2 raw35984step2Labels := by
      have ha : raw35984step2 = -raw35984step1 := by apply Matrix.ext; change ∀ i j, raw35984step2 i j = -(raw35984step1 i j); unfold raw35984step2 raw35984step1; decide +kernel
      have hl : raw35984step2Labels = raw35984step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35984step2 raw35984step2Labels = mixedMoment B raw35984step3 raw35984step3Labels := by
      have ha : raw35984step3 = raw35984step2 := by apply Matrix.ext; unfold raw35984step3 raw35984step2; decide +kernel
      have hl : raw35984step2Labels = labelEmbedding1 ∘ raw35984step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35984step2 raw35984step2Labels raw35984step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3053 node3053Labels := by rfl

def raw35985 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35985Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35985step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 3, -2], ![-1, 0, 1], ![-1, -1, 2]]
def raw35985step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35985step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw35985step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35985step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw35985step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35985 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35985 raw35985Labels = mixedMoment B node2238 node2238Labels := by
  calc
    mixedMoment B raw35985 raw35985Labels = mixedMoment B raw35985step0 raw35985step0Labels := by
      have ha : raw35985step0 = (fun i j => raw35985 (permutation212 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35985step0 raw35985; decide +kernel
      have hl : raw35985step0Labels = raw35985Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35985 raw35985Labels permutation212 permutation5
    mixedMoment B raw35985step0 raw35985step0Labels = mixedMoment B raw35985step1 raw35985step1Labels := by
      have ha : raw35985step1 = -raw35985step0 := by apply Matrix.ext; change ∀ i j, raw35985step1 i j = -(raw35985step0 i j); unfold raw35985step1 raw35985step0; decide +kernel
      have hl : raw35985step1Labels = raw35985step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35985step1 raw35985step1Labels = mixedMoment B raw35985step2 raw35985step2Labels := by
      have ha : raw35985step2 = raw35985step1 := by apply Matrix.ext; unfold raw35985step2 raw35985step1; decide +kernel
      have hl : raw35985step1Labels = labelEmbedding1 ∘ raw35985step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35985step1 raw35985step1Labels raw35985step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2238 node2238Labels := by rfl

def raw35986 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 0, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35986Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35986step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw35986step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35986step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw35986step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35986step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw35986step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35986 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35986 raw35986Labels = mixedMoment B node2150 node2150Labels := by
  calc
    mixedMoment B raw35986 raw35986Labels = mixedMoment B raw35986step0 raw35986step0Labels := by
      have ha : raw35986step0 = (fun i j => raw35986 (permutation265 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35986step0 raw35986; decide +kernel
      have hl : raw35986step0Labels = raw35986Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35986 raw35986Labels permutation265 permutation7
    mixedMoment B raw35986step0 raw35986step0Labels = mixedMoment B raw35986step1 raw35986step1Labels := by
      have ha : raw35986step1 = -raw35986step0 := by apply Matrix.ext; change ∀ i j, raw35986step1 i j = -(raw35986step0 i j); unfold raw35986step1 raw35986step0; decide +kernel
      have hl : raw35986step1Labels = raw35986step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35986step1 raw35986step1Labels = mixedMoment B raw35986step2 raw35986step2Labels := by
      have ha : raw35986step2 = raw35986step1 := by apply Matrix.ext; unfold raw35986step2 raw35986step1; decide +kernel
      have hl : raw35986step1Labels = labelEmbedding1 ∘ raw35986step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35986step1 raw35986step1Labels raw35986step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2150 node2150Labels := by rfl

def raw35987 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35987Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35987step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw35987step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35987step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw35987step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35987step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw35987step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35987 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35987 raw35987Labels = mixedMoment B node2669 node2669Labels := by
  calc
    mixedMoment B raw35987 raw35987Labels = mixedMoment B raw35987step0 raw35987step0Labels := by
      have ha : raw35987step0 = (fun i j => raw35987 (permutation265 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35987step0 raw35987; decide +kernel
      have hl : raw35987step0Labels = raw35987Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35987 raw35987Labels permutation265 permutation7
    mixedMoment B raw35987step0 raw35987step0Labels = mixedMoment B raw35987step1 raw35987step1Labels := by
      have ha : raw35987step1 = -raw35987step0 := by apply Matrix.ext; change ∀ i j, raw35987step1 i j = -(raw35987step0 i j); unfold raw35987step1 raw35987step0; decide +kernel
      have hl : raw35987step1Labels = raw35987step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35987step1 raw35987step1Labels = mixedMoment B raw35987step2 raw35987step2Labels := by
      have ha : raw35987step2 = raw35987step1 := by apply Matrix.ext; unfold raw35987step2 raw35987step1; decide +kernel
      have hl : raw35987step1Labels = labelEmbedding1 ∘ raw35987step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35987step1 raw35987step1Labels raw35987step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2669 node2669Labels := by rfl

def raw35988 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw35988Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35988step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw35988step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35988step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw35988step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35988step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw35988step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35988 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35988 raw35988Labels = mixedMoment B node2669 node2669Labels := by
  calc
    mixedMoment B raw35988 raw35988Labels = mixedMoment B raw35988step0 raw35988step0Labels := by
      have ha : raw35988step0 = (fun i j => raw35988 (permutation267 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35988step0 raw35988; decide +kernel
      have hl : raw35988step0Labels = raw35988Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35988 raw35988Labels permutation267 permutation7
    mixedMoment B raw35988step0 raw35988step0Labels = mixedMoment B raw35988step1 raw35988step1Labels := by
      have ha : raw35988step1 = -raw35988step0 := by apply Matrix.ext; change ∀ i j, raw35988step1 i j = -(raw35988step0 i j); unfold raw35988step1 raw35988step0; decide +kernel
      have hl : raw35988step1Labels = raw35988step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35988step1 raw35988step1Labels = mixedMoment B raw35988step2 raw35988step2Labels := by
      have ha : raw35988step2 = raw35988step1 := by apply Matrix.ext; unfold raw35988step2 raw35988step1; decide +kernel
      have hl : raw35988step1Labels = labelEmbedding1 ∘ raw35988step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35988step1 raw35988step1Labels raw35988step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2669 node2669Labels := by rfl

def raw35989 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw35989Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35989step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw35989step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35989step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw35989step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35989step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw35989step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35989 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35989 raw35989Labels = mixedMoment B node2671 node2671Labels := by
  calc
    mixedMoment B raw35989 raw35989Labels = mixedMoment B raw35989step0 raw35989step0Labels := by
      have ha : raw35989step0 = (fun i j => raw35989 (permutation265 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35989step0 raw35989; decide +kernel
      have hl : raw35989step0Labels = raw35989Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35989 raw35989Labels permutation265 permutation7
    mixedMoment B raw35989step0 raw35989step0Labels = mixedMoment B raw35989step1 raw35989step1Labels := by
      have ha : raw35989step1 = -raw35989step0 := by apply Matrix.ext; change ∀ i j, raw35989step1 i j = -(raw35989step0 i j); unfold raw35989step1 raw35989step0; decide +kernel
      have hl : raw35989step1Labels = raw35989step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35989step1 raw35989step1Labels = mixedMoment B raw35989step2 raw35989step2Labels := by
      have ha : raw35989step2 = raw35989step1 := by apply Matrix.ext; unfold raw35989step2 raw35989step1; decide +kernel
      have hl : raw35989step1Labels = labelEmbedding1 ∘ raw35989step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35989step1 raw35989step1Labels raw35989step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2671 node2671Labels := by rfl

def raw35990 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35990Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35990step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35990step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35990step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 3, -2], ![-1, -1, 2], ![-1, -1, 2]]
def raw35990step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35990step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -3, 2], ![1, 1, -2], ![1, 1, -2]]
def raw35990step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35990step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -3, 2], ![1, 1, -2], ![1, 1, -2]]
def raw35990step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35990 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35990 raw35990Labels = mixedMoment B node2257 node2257Labels := by
  calc
    mixedMoment B raw35990 raw35990Labels = mixedMoment B raw35990step0 raw35990step0Labels := by
      have hz : ∀ j, raw35990 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35990step0 = (fun i j => raw35990 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35990step0 raw35990; decide +kernel
      have hl : raw35990step0Labels = raw35990Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35990 raw35990Labels permutation346 hz
    mixedMoment B raw35990step0 raw35990step0Labels = mixedMoment B raw35990step1 raw35990step1Labels := by
      have ha : raw35990step1 = (fun i j => raw35990step0 (permutation44 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35990step1 raw35990step0; decide +kernel
      have hl : raw35990step1Labels = raw35990step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35990step0 raw35990step0Labels permutation44 permutation5
    mixedMoment B raw35990step1 raw35990step1Labels = mixedMoment B raw35990step2 raw35990step2Labels := by
      have ha : raw35990step2 = -raw35990step1 := by apply Matrix.ext; change ∀ i j, raw35990step2 i j = -(raw35990step1 i j); unfold raw35990step2 raw35990step1; decide +kernel
      have hl : raw35990step2Labels = raw35990step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35990step2 raw35990step2Labels = mixedMoment B raw35990step3 raw35990step3Labels := by
      have ha : raw35990step3 = raw35990step2 := by apply Matrix.ext; unfold raw35990step3 raw35990step2; decide +kernel
      have hl : raw35990step2Labels = labelEmbedding1 ∘ raw35990step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35990step2 raw35990step2Labels raw35990step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2257 node2257Labels := by rfl

def raw35991 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 0, 3], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35991Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35991step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 0, 3], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35991step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35991step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw35991step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35991step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw35991step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35991step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw35991step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35991 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35991 raw35991Labels = mixedMoment B node2166 node2166Labels := by
  calc
    mixedMoment B raw35991 raw35991Labels = mixedMoment B raw35991step0 raw35991step0Labels := by
      have hz : ∀ j, raw35991 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35991step0 = (fun i j => raw35991 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35991step0 raw35991; decide +kernel
      have hl : raw35991step0Labels = raw35991Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35991 raw35991Labels permutation346 hz
    mixedMoment B raw35991step0 raw35991step0Labels = mixedMoment B raw35991step1 raw35991step1Labels := by
      have ha : raw35991step1 = (fun i j => raw35991step0 (permutation58 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35991step1 raw35991step0; decide +kernel
      have hl : raw35991step1Labels = raw35991step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35991step0 raw35991step0Labels permutation58 permutation7
    mixedMoment B raw35991step1 raw35991step1Labels = mixedMoment B raw35991step2 raw35991step2Labels := by
      have ha : raw35991step2 = -raw35991step1 := by apply Matrix.ext; change ∀ i j, raw35991step2 i j = -(raw35991step1 i j); unfold raw35991step2 raw35991step1; decide +kernel
      have hl : raw35991step2Labels = raw35991step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35991step2 raw35991step2Labels = mixedMoment B raw35991step3 raw35991step3Labels := by
      have ha : raw35991step3 = raw35991step2 := by apply Matrix.ext; unfold raw35991step3 raw35991step2; decide +kernel
      have hl : raw35991step2Labels = labelEmbedding1 ∘ raw35991step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35991step2 raw35991step2Labels raw35991step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2166 node2166Labels := by rfl

def raw35992 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![-1, 1, 0], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35992Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35992step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw35992step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35992step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw35992step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35992step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw35992step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35992 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35992 raw35992Labels = mixedMoment B node2656 node2656Labels := by
  calc
    mixedMoment B raw35992 raw35992Labels = mixedMoment B raw35992step0 raw35992step0Labels := by
      have ha : raw35992step0 = (fun i j => raw35992 (permutation267 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35992step0 raw35992; decide +kernel
      have hl : raw35992step0Labels = raw35992Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35992 raw35992Labels permutation267 permutation7
    mixedMoment B raw35992step0 raw35992step0Labels = mixedMoment B raw35992step1 raw35992step1Labels := by
      have ha : raw35992step1 = -raw35992step0 := by apply Matrix.ext; change ∀ i j, raw35992step1 i j = -(raw35992step0 i j); unfold raw35992step1 raw35992step0; decide +kernel
      have hl : raw35992step1Labels = raw35992step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35992step1 raw35992step1Labels = mixedMoment B raw35992step2 raw35992step2Labels := by
      have ha : raw35992step2 = raw35992step1 := by apply Matrix.ext; unfold raw35992step2 raw35992step1; decide +kernel
      have hl : raw35992step1Labels = labelEmbedding1 ∘ raw35992step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35992step1 raw35992step1Labels raw35992step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2656 node2656Labels := by rfl

def raw35993 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![0, 0, 0], ![2, -1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw35993Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35993step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![2, -1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw35993step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35993step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw35993step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35993step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw35993step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35993step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw35993step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35993 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35993 raw35993Labels = mixedMoment B node2682 node2682Labels := by
  calc
    mixedMoment B raw35993 raw35993Labels = mixedMoment B raw35993step0 raw35993step0Labels := by
      have hz : ∀ j, raw35993 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35993step0 = (fun i j => raw35993 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35993step0 raw35993; decide +kernel
      have hl : raw35993step0Labels = raw35993Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35993 raw35993Labels permutation346 hz
    mixedMoment B raw35993step0 raw35993step0Labels = mixedMoment B raw35993step1 raw35993step1Labels := by
      have ha : raw35993step1 = (fun i j => raw35993step0 (permutation58 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35993step1 raw35993step0; decide +kernel
      have hl : raw35993step1Labels = raw35993step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35993step0 raw35993step0Labels permutation58 permutation7
    mixedMoment B raw35993step1 raw35993step1Labels = mixedMoment B raw35993step2 raw35993step2Labels := by
      have ha : raw35993step2 = -raw35993step1 := by apply Matrix.ext; change ∀ i j, raw35993step2 i j = -(raw35993step1 i j); unfold raw35993step2 raw35993step1; decide +kernel
      have hl : raw35993step2Labels = raw35993step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35993step2 raw35993step2Labels = mixedMoment B raw35993step3 raw35993step3Labels := by
      have ha : raw35993step3 = raw35993step2 := by apply Matrix.ext; unfold raw35993step3 raw35993step2; decide +kernel
      have hl : raw35993step2Labels = labelEmbedding1 ∘ raw35993step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35993step2 raw35993step2Labels raw35993step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2682 node2682Labels := by rfl

def raw35994 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw35994Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35994step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw35994step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35994step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw35994step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35994step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw35994step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35994step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw35994step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35994 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35994 raw35994Labels = mixedMoment B node2684 node2684Labels := by
  calc
    mixedMoment B raw35994 raw35994Labels = mixedMoment B raw35994step0 raw35994step0Labels := by
      have hz : ∀ j, raw35994 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35994step0 = (fun i j => raw35994 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35994step0 raw35994; decide +kernel
      have hl : raw35994step0Labels = raw35994Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35994 raw35994Labels permutation346 hz
    mixedMoment B raw35994step0 raw35994step0Labels = mixedMoment B raw35994step1 raw35994step1Labels := by
      have ha : raw35994step1 = (fun i j => raw35994step0 (permutation59 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35994step1 raw35994step0; decide +kernel
      have hl : raw35994step1Labels = raw35994step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35994step0 raw35994step0Labels permutation59 permutation7
    mixedMoment B raw35994step1 raw35994step1Labels = mixedMoment B raw35994step2 raw35994step2Labels := by
      have ha : raw35994step2 = -raw35994step1 := by apply Matrix.ext; change ∀ i j, raw35994step2 i j = -(raw35994step1 i j); unfold raw35994step2 raw35994step1; decide +kernel
      have hl : raw35994step2Labels = raw35994step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35994step2 raw35994step2Labels = mixedMoment B raw35994step3 raw35994step3Labels := by
      have ha : raw35994step3 = raw35994step2 := by apply Matrix.ext; unfold raw35994step3 raw35994step2; decide +kernel
      have hl : raw35994step2Labels = labelEmbedding1 ∘ raw35994step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35994step2 raw35994step2Labels raw35994step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2684 node2684Labels := by rfl

def raw35995 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35995Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35995step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35995step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35995step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 3, -2], ![-1, -1, 2], ![-1, -1, 2]]
def raw35995step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35995step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -3, 2], ![1, 1, -2], ![1, 1, -2]]
def raw35995step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35995step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -3, 2], ![1, 1, -2], ![1, 1, -2]]
def raw35995step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35995 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35995 raw35995Labels = mixedMoment B node2257 node2257Labels := by
  calc
    mixedMoment B raw35995 raw35995Labels = mixedMoment B raw35995step0 raw35995step0Labels := by
      have hz : ∀ j, raw35995 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35995step0 = (fun i j => raw35995 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35995step0 raw35995; decide +kernel
      have hl : raw35995step0Labels = raw35995Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35995 raw35995Labels permutation346 hz
    mixedMoment B raw35995step0 raw35995step0Labels = mixedMoment B raw35995step1 raw35995step1Labels := by
      have ha : raw35995step1 = (fun i j => raw35995step0 (permutation38 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35995step1 raw35995step0; decide +kernel
      have hl : raw35995step1Labels = raw35995step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35995step0 raw35995step0Labels permutation38 permutation5
    mixedMoment B raw35995step1 raw35995step1Labels = mixedMoment B raw35995step2 raw35995step2Labels := by
      have ha : raw35995step2 = -raw35995step1 := by apply Matrix.ext; change ∀ i j, raw35995step2 i j = -(raw35995step1 i j); unfold raw35995step2 raw35995step1; decide +kernel
      have hl : raw35995step2Labels = raw35995step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35995step2 raw35995step2Labels = mixedMoment B raw35995step3 raw35995step3Labels := by
      have ha : raw35995step3 = raw35995step2 := by apply Matrix.ext; unfold raw35995step3 raw35995step2; decide +kernel
      have hl : raw35995step2Labels = labelEmbedding1 ∘ raw35995step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35995step2 raw35995step2Labels raw35995step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2257 node2257Labels := by rfl

def raw35996 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 0, 3], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35996Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35996step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 0, 3], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35996step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35996step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw35996step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35996step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw35996step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35996step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw35996step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35996 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35996 raw35996Labels = mixedMoment B node2166 node2166Labels := by
  calc
    mixedMoment B raw35996 raw35996Labels = mixedMoment B raw35996step0 raw35996step0Labels := by
      have hz : ∀ j, raw35996 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35996step0 = (fun i j => raw35996 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35996step0 raw35996; decide +kernel
      have hl : raw35996step0Labels = raw35996Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35996 raw35996Labels permutation346 hz
    mixedMoment B raw35996step0 raw35996step0Labels = mixedMoment B raw35996step1 raw35996step1Labels := by
      have ha : raw35996step1 = (fun i j => raw35996step0 (permutation56 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35996step1 raw35996step0; decide +kernel
      have hl : raw35996step1Labels = raw35996step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35996step0 raw35996step0Labels permutation56 permutation7
    mixedMoment B raw35996step1 raw35996step1Labels = mixedMoment B raw35996step2 raw35996step2Labels := by
      have ha : raw35996step2 = -raw35996step1 := by apply Matrix.ext; change ∀ i j, raw35996step2 i j = -(raw35996step1 i j); unfold raw35996step2 raw35996step1; decide +kernel
      have hl : raw35996step2Labels = raw35996step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35996step2 raw35996step2Labels = mixedMoment B raw35996step3 raw35996step3Labels := by
      have ha : raw35996step3 = raw35996step2 := by apply Matrix.ext; unfold raw35996step3 raw35996step2; decide +kernel
      have hl : raw35996step2Labels = labelEmbedding1 ∘ raw35996step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35996step2 raw35996step2Labels raw35996step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2166 node2166Labels := by rfl

def raw35997 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35997Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35997step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw35997step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35997step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw35997step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35997step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw35997step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35997 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35997 raw35997Labels = mixedMoment B node2656 node2656Labels := by
  calc
    mixedMoment B raw35997 raw35997Labels = mixedMoment B raw35997step0 raw35997step0Labels := by
      have ha : raw35997step0 = (fun i j => raw35997 (permutation265 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35997step0 raw35997; decide +kernel
      have hl : raw35997step0Labels = raw35997Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35997 raw35997Labels permutation265 permutation7
    mixedMoment B raw35997step0 raw35997step0Labels = mixedMoment B raw35997step1 raw35997step1Labels := by
      have ha : raw35997step1 = -raw35997step0 := by apply Matrix.ext; change ∀ i j, raw35997step1 i j = -(raw35997step0 i j); unfold raw35997step1 raw35997step0; decide +kernel
      have hl : raw35997step1Labels = raw35997step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35997step1 raw35997step1Labels = mixedMoment B raw35997step2 raw35997step2Labels := by
      have ha : raw35997step2 = raw35997step1 := by apply Matrix.ext; unfold raw35997step2 raw35997step1; decide +kernel
      have hl : raw35997step1Labels = labelEmbedding1 ∘ raw35997step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35997step1 raw35997step1Labels raw35997step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2656 node2656Labels := by rfl

def raw35998 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35998Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35998step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35998step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35998step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw35998step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35998step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw35998step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35998step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw35998step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35998 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35998 raw35998Labels = mixedMoment B node2682 node2682Labels := by
  calc
    mixedMoment B raw35998 raw35998Labels = mixedMoment B raw35998step0 raw35998step0Labels := by
      have hz : ∀ j, raw35998 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35998step0 = (fun i j => raw35998 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35998step0 raw35998; decide +kernel
      have hl : raw35998step0Labels = raw35998Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35998 raw35998Labels permutation346 hz
    mixedMoment B raw35998step0 raw35998step0Labels = mixedMoment B raw35998step1 raw35998step1Labels := by
      have ha : raw35998step1 = (fun i j => raw35998step0 (permutation56 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35998step1 raw35998step0; decide +kernel
      have hl : raw35998step1Labels = raw35998step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35998step0 raw35998step0Labels permutation56 permutation7
    mixedMoment B raw35998step1 raw35998step1Labels = mixedMoment B raw35998step2 raw35998step2Labels := by
      have ha : raw35998step2 = -raw35998step1 := by apply Matrix.ext; change ∀ i j, raw35998step2 i j = -(raw35998step1 i j); unfold raw35998step2 raw35998step1; decide +kernel
      have hl : raw35998step2Labels = raw35998step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35998step2 raw35998step2Labels = mixedMoment B raw35998step3 raw35998step3Labels := by
      have ha : raw35998step3 = raw35998step2 := by apply Matrix.ext; unfold raw35998step3 raw35998step2; decide +kernel
      have hl : raw35998step2Labels = labelEmbedding1 ∘ raw35998step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35998step2 raw35998step2Labels raw35998step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2682 node2682Labels := by rfl

def raw35999 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw35999Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35999step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw35999step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35999step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw35999step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35999step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw35999step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35999step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw35999step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35999 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35999 raw35999Labels = mixedMoment B node2684 node2684Labels := by
  calc
    mixedMoment B raw35999 raw35999Labels = mixedMoment B raw35999step0 raw35999step0Labels := by
      have hz : ∀ j, raw35999 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35999step0 = (fun i j => raw35999 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35999step0 raw35999; decide +kernel
      have hl : raw35999step0Labels = raw35999Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35999 raw35999Labels permutation346 hz
    mixedMoment B raw35999step0 raw35999step0Labels = mixedMoment B raw35999step1 raw35999step1Labels := by
      have ha : raw35999step1 = (fun i j => raw35999step0 (permutation57 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35999step1 raw35999step0; decide +kernel
      have hl : raw35999step1Labels = raw35999step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35999step0 raw35999step0Labels permutation57 permutation7
    mixedMoment B raw35999step1 raw35999step1Labels = mixedMoment B raw35999step2 raw35999step2Labels := by
      have ha : raw35999step2 = -raw35999step1 := by apply Matrix.ext; change ∀ i j, raw35999step2 i j = -(raw35999step1 i j); unfold raw35999step2 raw35999step1; decide +kernel
      have hl : raw35999step2Labels = raw35999step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35999step2 raw35999step2Labels = mixedMoment B raw35999step3 raw35999step3Labels := by
      have ha : raw35999step3 = raw35999step2 := by apply Matrix.ext; unfold raw35999step3 raw35999step2; decide +kernel
      have hl : raw35999step2Labels = labelEmbedding1 ∘ raw35999step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35999step2 raw35999step2Labels raw35999step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2684 node2684Labels := by rfl

def raw36000 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw36000Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36000step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw36000step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36000step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 3, -2], ![-2, -1, 3]]
def raw36000step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36000step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 1, -3]]
def raw36000step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36000step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 1, -3]]
def raw36000step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36000 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36000 raw36000Labels = mixedMoment B node2239 node2239Labels := by
  calc
    mixedMoment B raw36000 raw36000Labels = mixedMoment B raw36000step0 raw36000step0Labels := by
      have hz : ∀ j, raw36000 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36000step0 = (fun i j => raw36000 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36000step0 raw36000; decide +kernel
      have hl : raw36000step0Labels = raw36000Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36000 raw36000Labels permutation346 hz
    mixedMoment B raw36000step0 raw36000step0Labels = mixedMoment B raw36000step1 raw36000step1Labels := by
      have ha : raw36000step1 = (fun i j => raw36000step0 (permutation40 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36000step1 raw36000step0; decide +kernel
      have hl : raw36000step1Labels = raw36000step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36000step0 raw36000step0Labels permutation40 permutation5
    mixedMoment B raw36000step1 raw36000step1Labels = mixedMoment B raw36000step2 raw36000step2Labels := by
      have ha : raw36000step2 = -raw36000step1 := by apply Matrix.ext; change ∀ i j, raw36000step2 i j = -(raw36000step1 i j); unfold raw36000step2 raw36000step1; decide +kernel
      have hl : raw36000step2Labels = raw36000step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36000step2 raw36000step2Labels = mixedMoment B raw36000step3 raw36000step3Labels := by
      have ha : raw36000step3 = raw36000step2 := by apply Matrix.ext; unfold raw36000step3 raw36000step2; decide +kernel
      have hl : raw36000step2Labels = labelEmbedding1 ∘ raw36000step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36000step2 raw36000step2Labels raw36000step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2239 node2239Labels := by rfl

def raw36001 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 0, 3], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw36001Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36001step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 0, 3], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw36001step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36001step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw36001step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36001step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw36001step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36001step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw36001step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36001 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36001 raw36001Labels = mixedMoment B node2165 node2165Labels := by
  calc
    mixedMoment B raw36001 raw36001Labels = mixedMoment B raw36001step0 raw36001step0Labels := by
      have hz : ∀ j, raw36001 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36001step0 = (fun i j => raw36001 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36001step0 raw36001; decide +kernel
      have hl : raw36001step0Labels = raw36001Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36001 raw36001Labels permutation346 hz
    mixedMoment B raw36001step0 raw36001step0Labels = mixedMoment B raw36001step1 raw36001step1Labels := by
      have ha : raw36001step1 = (fun i j => raw36001step0 (permutation56 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36001step1 raw36001step0; decide +kernel
      have hl : raw36001step1Labels = raw36001step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36001step0 raw36001step0Labels permutation56 permutation7
    mixedMoment B raw36001step1 raw36001step1Labels = mixedMoment B raw36001step2 raw36001step2Labels := by
      have ha : raw36001step2 = -raw36001step1 := by apply Matrix.ext; change ∀ i j, raw36001step2 i j = -(raw36001step1 i j); unfold raw36001step2 raw36001step1; decide +kernel
      have hl : raw36001step2Labels = raw36001step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36001step2 raw36001step2Labels = mixedMoment B raw36001step3 raw36001step3Labels := by
      have ha : raw36001step3 = raw36001step2 := by apply Matrix.ext; unfold raw36001step3 raw36001step2; decide +kernel
      have hl : raw36001step2Labels = labelEmbedding1 ∘ raw36001step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36001step2 raw36001step2Labels raw36001step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2165 node2165Labels := by rfl

def raw36002 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw36002Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36002step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw36002step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36002step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw36002step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36002step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw36002step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36002 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36002 raw36002Labels = mixedMoment B node2655 node2655Labels := by
  calc
    mixedMoment B raw36002 raw36002Labels = mixedMoment B raw36002step0 raw36002step0Labels := by
      have ha : raw36002step0 = (fun i j => raw36002 (permutation265 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36002step0 raw36002; decide +kernel
      have hl : raw36002step0Labels = raw36002Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36002 raw36002Labels permutation265 permutation7
    mixedMoment B raw36002step0 raw36002step0Labels = mixedMoment B raw36002step1 raw36002step1Labels := by
      have ha : raw36002step1 = -raw36002step0 := by apply Matrix.ext; change ∀ i j, raw36002step1 i j = -(raw36002step0 i j); unfold raw36002step1 raw36002step0; decide +kernel
      have hl : raw36002step1Labels = raw36002step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36002step1 raw36002step1Labels = mixedMoment B raw36002step2 raw36002step2Labels := by
      have ha : raw36002step2 = raw36002step1 := by apply Matrix.ext; unfold raw36002step2 raw36002step1; decide +kernel
      have hl : raw36002step1Labels = labelEmbedding1 ∘ raw36002step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36002step1 raw36002step1Labels raw36002step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2655 node2655Labels := by rfl

def raw36003 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw36003Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36003step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw36003step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36003step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw36003step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36003step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw36003step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36003step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw36003step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36003 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36003 raw36003Labels = mixedMoment B node2681 node2681Labels := by
  calc
    mixedMoment B raw36003 raw36003Labels = mixedMoment B raw36003step0 raw36003step0Labels := by
      have hz : ∀ j, raw36003 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36003step0 = (fun i j => raw36003 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36003step0 raw36003; decide +kernel
      have hl : raw36003step0Labels = raw36003Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36003 raw36003Labels permutation346 hz
    mixedMoment B raw36003step0 raw36003step0Labels = mixedMoment B raw36003step1 raw36003step1Labels := by
      have ha : raw36003step1 = (fun i j => raw36003step0 (permutation56 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36003step1 raw36003step0; decide +kernel
      have hl : raw36003step1Labels = raw36003step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36003step0 raw36003step0Labels permutation56 permutation7
    mixedMoment B raw36003step1 raw36003step1Labels = mixedMoment B raw36003step2 raw36003step2Labels := by
      have ha : raw36003step2 = -raw36003step1 := by apply Matrix.ext; change ∀ i j, raw36003step2 i j = -(raw36003step1 i j); unfold raw36003step2 raw36003step1; decide +kernel
      have hl : raw36003step2Labels = raw36003step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36003step2 raw36003step2Labels = mixedMoment B raw36003step3 raw36003step3Labels := by
      have ha : raw36003step3 = raw36003step2 := by apply Matrix.ext; unfold raw36003step3 raw36003step2; decide +kernel
      have hl : raw36003step2Labels = labelEmbedding1 ∘ raw36003step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36003step2 raw36003step2Labels raw36003step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2681 node2681Labels := by rfl

def raw36004 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![3, -2, -1]]
def raw36004Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36004step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![1, 0, -1], ![0, 1, -1], ![3, -2, -1]]
def raw36004step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36004step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw36004step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36004step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw36004step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36004step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw36004step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36004 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36004 raw36004Labels = mixedMoment B node2681 node2681Labels := by
  calc
    mixedMoment B raw36004 raw36004Labels = mixedMoment B raw36004step0 raw36004step0Labels := by
      have hz : ∀ j, raw36004 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36004step0 = (fun i j => raw36004 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36004step0 raw36004; decide +kernel
      have hl : raw36004step0Labels = raw36004Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36004 raw36004Labels permutation346 hz
    mixedMoment B raw36004step0 raw36004step0Labels = mixedMoment B raw36004step1 raw36004step1Labels := by
      have ha : raw36004step1 = (fun i j => raw36004step0 (permutation58 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36004step1 raw36004step0; decide +kernel
      have hl : raw36004step1Labels = raw36004step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36004step0 raw36004step0Labels permutation58 permutation7
    mixedMoment B raw36004step1 raw36004step1Labels = mixedMoment B raw36004step2 raw36004step2Labels := by
      have ha : raw36004step2 = -raw36004step1 := by apply Matrix.ext; change ∀ i j, raw36004step2 i j = -(raw36004step1 i j); unfold raw36004step2 raw36004step1; decide +kernel
      have hl : raw36004step2Labels = raw36004step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36004step2 raw36004step2Labels = mixedMoment B raw36004step3 raw36004step3Labels := by
      have ha : raw36004step3 = raw36004step2 := by apply Matrix.ext; unfold raw36004step3 raw36004step2; decide +kernel
      have hl : raw36004step2Labels = labelEmbedding1 ∘ raw36004step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36004step2 raw36004step2Labels raw36004step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2681 node2681Labels := by rfl

def raw36005 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![3, -1, -2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw36005Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36005step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw36005step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36005step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw36005step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36005 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36005 raw36005Labels = mixedMoment B node5013 node5013Labels := by
  calc
    mixedMoment B raw36005 raw36005Labels = mixedMoment B raw36005step0 raw36005step0Labels := by
      have ha : raw36005step0 = (fun i j => raw36005 (permutation265 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36005step0 raw36005; decide +kernel
      have hl : raw36005step0Labels = raw36005Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36005 raw36005Labels permutation265 permutation2
    mixedMoment B raw36005step0 raw36005step0Labels = mixedMoment B raw36005step1 raw36005step1Labels := by
      have ha : raw36005step1 = -raw36005step0 := by apply Matrix.ext; change ∀ i j, raw36005step1 i j = -(raw36005step0 i j); unfold raw36005step1 raw36005step0; decide +kernel
      have hl : raw36005step1Labels = raw36005step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5013 node5013Labels := by rfl

def raw36006 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![3, -1, -2], ![0, 0, 0], ![-2, 1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw36006Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36006step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![3, -1, -2], ![-2, 1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw36006step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36006step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw36006step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36006step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw36006step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36006 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36006 raw36006Labels = mixedMoment B node5018 node5018Labels := by
  calc
    mixedMoment B raw36006 raw36006Labels = mixedMoment B raw36006step0 raw36006step0Labels := by
      have hz : ∀ j, raw36006 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36006step0 = (fun i j => raw36006 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36006step0 raw36006; decide +kernel
      have hl : raw36006step0Labels = raw36006Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36006 raw36006Labels permutation346 hz
    mixedMoment B raw36006step0 raw36006step0Labels = mixedMoment B raw36006step1 raw36006step1Labels := by
      have ha : raw36006step1 = (fun i j => raw36006step0 (permutation59 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36006step1 raw36006step0; decide +kernel
      have hl : raw36006step1Labels = raw36006step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36006step0 raw36006step0Labels permutation59 permutation2
    mixedMoment B raw36006step1 raw36006step1Labels = mixedMoment B raw36006step2 raw36006step2Labels := by
      have ha : raw36006step2 = -raw36006step1 := by apply Matrix.ext; change ∀ i j, raw36006step2 i j = -(raw36006step1 i j); unfold raw36006step2 raw36006step1; decide +kernel
      have hl : raw36006step2Labels = raw36006step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5018 node5018Labels := by rfl

def raw36007 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![3, -1, -2], ![0, 0, 0], ![-1, 0, 1], ![-2, 1, 1], ![-1, -1, 2]]
def raw36007Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36007step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![3, -1, -2], ![-1, 0, 1], ![-2, 1, 1], ![-1, -1, 2]]
def raw36007step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36007step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw36007step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36007step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw36007step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36007 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36007 raw36007Labels = mixedMoment B node5018 node5018Labels := by
  calc
    mixedMoment B raw36007 raw36007Labels = mixedMoment B raw36007step0 raw36007step0Labels := by
      have hz : ∀ j, raw36007 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36007step0 = (fun i j => raw36007 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36007step0 raw36007; decide +kernel
      have hl : raw36007step0Labels = raw36007Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36007 raw36007Labels permutation346 hz
    mixedMoment B raw36007step0 raw36007step0Labels = mixedMoment B raw36007step1 raw36007step1Labels := by
      have ha : raw36007step1 = (fun i j => raw36007step0 (permutation57 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36007step1 raw36007step0; decide +kernel
      have hl : raw36007step1Labels = raw36007step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36007step0 raw36007step0Labels permutation57 permutation2
    mixedMoment B raw36007step1 raw36007step1Labels = mixedMoment B raw36007step2 raw36007step2Labels := by
      have ha : raw36007step2 = -raw36007step1 := by apply Matrix.ext; change ∀ i j, raw36007step2 i j = -(raw36007step1 i j); unfold raw36007step2 raw36007step1; decide +kernel
      have hl : raw36007step2Labels = raw36007step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5018 node5018Labels := by rfl

def raw36008 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![3, -1, -2], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw36008Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36008step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![3, -1, -2], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw36008step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36008step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw36008step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36008step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw36008step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36008 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36008 raw36008Labels = mixedMoment B node5017 node5017Labels := by
  calc
    mixedMoment B raw36008 raw36008Labels = mixedMoment B raw36008step0 raw36008step0Labels := by
      have hz : ∀ j, raw36008 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36008step0 = (fun i j => raw36008 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36008step0 raw36008; decide +kernel
      have hl : raw36008step0Labels = raw36008Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36008 raw36008Labels permutation346 hz
    mixedMoment B raw36008step0 raw36008step0Labels = mixedMoment B raw36008step1 raw36008step1Labels := by
      have ha : raw36008step1 = (fun i j => raw36008step0 (permutation56 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36008step1 raw36008step0; decide +kernel
      have hl : raw36008step1Labels = raw36008step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36008step0 raw36008step0Labels permutation56 permutation2
    mixedMoment B raw36008step1 raw36008step1Labels = mixedMoment B raw36008step2 raw36008step2Labels := by
      have ha : raw36008step2 = -raw36008step1 := by apply Matrix.ext; change ∀ i j, raw36008step2 i j = -(raw36008step1 i j); unfold raw36008step2 raw36008step1; decide +kernel
      have hl : raw36008step2Labels = raw36008step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5017 node5017Labels := by rfl

def raw36009 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![4, -2, -2], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw36009Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36009step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![4, -2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw36009step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36009step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![-1, 3, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw36009step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36009step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw36009step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36009 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36009 raw36009Labels = mixedMoment B node4613 node4613Labels := by
  calc
    mixedMoment B raw36009 raw36009Labels = mixedMoment B raw36009step0 raw36009step0Labels := by
      have hz : ∀ j, raw36009 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36009step0 = (fun i j => raw36009 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36009step0 raw36009; decide +kernel
      have hl : raw36009step0Labels = raw36009Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36009 raw36009Labels permutation346 hz
    mixedMoment B raw36009step0 raw36009step0Labels = mixedMoment B raw36009step1 raw36009step1Labels := by
      have ha : raw36009step1 = (fun i j => raw36009step0 (permutation56 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36009step1 raw36009step0; decide +kernel
      have hl : raw36009step1Labels = raw36009step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36009step0 raw36009step0Labels permutation56 permutation2
    mixedMoment B raw36009step1 raw36009step1Labels = mixedMoment B raw36009step2 raw36009step2Labels := by
      have ha : raw36009step2 = -raw36009step1 := by apply Matrix.ext; change ∀ i j, raw36009step2 i j = -(raw36009step1 i j); unfold raw36009step2 raw36009step1; decide +kernel
      have hl : raw36009step2Labels = raw36009step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4613 node4613Labels := by rfl

def raw36010 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![4, -2, -2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw36010Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36010step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -2, -2], ![0, 2, -2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw36010step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36010step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw36010step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36010 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36010 raw36010Labels = mixedMoment B node4566 node4566Labels := by
  calc
    mixedMoment B raw36010 raw36010Labels = mixedMoment B raw36010step0 raw36010step0Labels := by
      have ha : raw36010step0 = (fun i j => raw36010 (permutation265 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36010step0 raw36010; decide +kernel
      have hl : raw36010step0Labels = raw36010Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36010 raw36010Labels permutation265 permutation2
    mixedMoment B raw36010step0 raw36010step0Labels = mixedMoment B raw36010step1 raw36010step1Labels := by
      have ha : raw36010step1 = -raw36010step0 := by apply Matrix.ext; change ∀ i j, raw36010step1 i j = -(raw36010step0 i j); unfold raw36010step1 raw36010step0; decide +kernel
      have hl : raw36010step1Labels = raw36010step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4566 node4566Labels := by rfl

def raw36011 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![4, -2, -2], ![0, 0, 0], ![-2, 1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw36011Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36011step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![4, -2, -2], ![-2, 1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw36011step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36011step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![0, 2, -2], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw36011step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36011step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw36011step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36011 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36011 raw36011Labels = mixedMoment B node4571 node4571Labels := by
  calc
    mixedMoment B raw36011 raw36011Labels = mixedMoment B raw36011step0 raw36011step0Labels := by
      have hz : ∀ j, raw36011 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36011step0 = (fun i j => raw36011 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36011step0 raw36011; decide +kernel
      have hl : raw36011step0Labels = raw36011Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36011 raw36011Labels permutation346 hz
    mixedMoment B raw36011step0 raw36011step0Labels = mixedMoment B raw36011step1 raw36011step1Labels := by
      have ha : raw36011step1 = (fun i j => raw36011step0 (permutation59 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36011step1 raw36011step0; decide +kernel
      have hl : raw36011step1Labels = raw36011step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36011step0 raw36011step0Labels permutation59 permutation2
    mixedMoment B raw36011step1 raw36011step1Labels = mixedMoment B raw36011step2 raw36011step2Labels := by
      have ha : raw36011step2 = -raw36011step1 := by apply Matrix.ext; change ∀ i j, raw36011step2 i j = -(raw36011step1 i j); unfold raw36011step2 raw36011step1; decide +kernel
      have hl : raw36011step2Labels = raw36011step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4571 node4571Labels := by rfl

def raw36012 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![4, -2, -2], ![0, 0, 0], ![-1, 0, 1], ![-2, 1, 1], ![-1, -1, 2]]
def raw36012Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36012step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![4, -2, -2], ![-1, 0, 1], ![-2, 1, 1], ![-1, -1, 2]]
def raw36012step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36012step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![0, 2, -2], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw36012step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36012step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw36012step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36012 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36012 raw36012Labels = mixedMoment B node4571 node4571Labels := by
  calc
    mixedMoment B raw36012 raw36012Labels = mixedMoment B raw36012step0 raw36012step0Labels := by
      have hz : ∀ j, raw36012 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36012step0 = (fun i j => raw36012 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36012step0 raw36012; decide +kernel
      have hl : raw36012step0Labels = raw36012Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36012 raw36012Labels permutation346 hz
    mixedMoment B raw36012step0 raw36012step0Labels = mixedMoment B raw36012step1 raw36012step1Labels := by
      have ha : raw36012step1 = (fun i j => raw36012step0 (permutation57 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36012step1 raw36012step0; decide +kernel
      have hl : raw36012step1Labels = raw36012step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36012step0 raw36012step0Labels permutation57 permutation2
    mixedMoment B raw36012step1 raw36012step1Labels = mixedMoment B raw36012step2 raw36012step2Labels := by
      have ha : raw36012step2 = -raw36012step1 := by apply Matrix.ext; change ∀ i j, raw36012step2 i j = -(raw36012step1 i j); unfold raw36012step2 raw36012step1; decide +kernel
      have hl : raw36012step2Labels = raw36012step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4571 node4571Labels := by rfl

def raw36013 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![4, -2, -2], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw36013Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36013step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![4, -2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw36013step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36013step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw36013step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36013step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw36013step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36013 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36013 raw36013Labels = mixedMoment B node4570 node4570Labels := by
  calc
    mixedMoment B raw36013 raw36013Labels = mixedMoment B raw36013step0 raw36013step0Labels := by
      have hz : ∀ j, raw36013 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36013step0 = (fun i j => raw36013 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36013step0 raw36013; decide +kernel
      have hl : raw36013step0Labels = raw36013Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36013 raw36013Labels permutation346 hz
    mixedMoment B raw36013step0 raw36013step0Labels = mixedMoment B raw36013step1 raw36013step1Labels := by
      have ha : raw36013step1 = (fun i j => raw36013step0 (permutation56 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36013step1 raw36013step0; decide +kernel
      have hl : raw36013step1Labels = raw36013step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36013step0 raw36013step0Labels permutation56 permutation2
    mixedMoment B raw36013step1 raw36013step1Labels = mixedMoment B raw36013step2 raw36013step2Labels := by
      have ha : raw36013step2 = -raw36013step1 := by apply Matrix.ext; change ∀ i j, raw36013step2 i j = -(raw36013step1 i j); unfold raw36013step2 raw36013step1; decide +kernel
      have hl : raw36013step2Labels = raw36013step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4570 node4570Labels := by rfl

def raw36014 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![3, -1, -2], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw36014Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36014step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![3, -1, -2], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw36014step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36014step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 3, -2], ![-1, 0, 1], ![-1, -1, 2]]
def raw36014step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36014step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw36014step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36014 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36014 raw36014Labels = mixedMoment B node5288 node5288Labels := by
  calc
    mixedMoment B raw36014 raw36014Labels = mixedMoment B raw36014step0 raw36014step0Labels := by
      have hz : ∀ j, raw36014 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36014step0 = (fun i j => raw36014 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36014step0 raw36014; decide +kernel
      have hl : raw36014step0Labels = raw36014Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36014 raw36014Labels permutation346 hz
    mixedMoment B raw36014step0 raw36014step0Labels = mixedMoment B raw36014step1 raw36014step1Labels := by
      have ha : raw36014step1 = (fun i j => raw36014step0 (permutation62 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36014step1 raw36014step0; decide +kernel
      have hl : raw36014step1Labels = raw36014step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36014step0 raw36014step0Labels permutation62 permutation2
    mixedMoment B raw36014step1 raw36014step1Labels = mixedMoment B raw36014step2 raw36014step2Labels := by
      have ha : raw36014step2 = -raw36014step1 := by apply Matrix.ext; change ∀ i j, raw36014step2 i j = -(raw36014step1 i j); unfold raw36014step2 raw36014step1; decide +kernel
      have hl : raw36014step2Labels = raw36014step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5288 node5288Labels := by rfl

def raw36015 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -1, -2], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw36015Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36015step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw36015step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36015step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw36015step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36015 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36015 raw36015Labels = mixedMoment B node5226 node5226Labels := by
  calc
    mixedMoment B raw36015 raw36015Labels = mixedMoment B raw36015step0 raw36015step0Labels := by
      have ha : raw36015step0 = (fun i j => raw36015 (permutation271 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36015step0 raw36015; decide +kernel
      have hl : raw36015step0Labels = raw36015Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36015 raw36015Labels permutation271 permutation2
    mixedMoment B raw36015step0 raw36015step0Labels = mixedMoment B raw36015step1 raw36015step1Labels := by
      have ha : raw36015step1 = -raw36015step0 := by apply Matrix.ext; change ∀ i j, raw36015step1 i j = -(raw36015step0 i j); unfold raw36015step1 raw36015step0; decide +kernel
      have hl : raw36015step1Labels = raw36015step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5226 node5226Labels := by rfl

def raw36016 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -1, -2], ![0, 0, 0], ![0, -1, 1], ![-2, 1, 1], ![-1, -1, 2]]
def raw36016Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36016step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![3, -1, -2], ![0, -1, 1], ![-2, 1, 1], ![-1, -1, 2]]
def raw36016step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36016step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw36016step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36016step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw36016step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36016 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36016 raw36016Labels = mixedMoment B node5229 node5229Labels := by
  calc
    mixedMoment B raw36016 raw36016Labels = mixedMoment B raw36016step0 raw36016step0Labels := by
      have hz : ∀ j, raw36016 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36016step0 = (fun i j => raw36016 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36016step0 raw36016; decide +kernel
      have hl : raw36016step0Labels = raw36016Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36016 raw36016Labels permutation346 hz
    mixedMoment B raw36016step0 raw36016step0Labels = mixedMoment B raw36016step1 raw36016step1Labels := by
      have ha : raw36016step1 = (fun i j => raw36016step0 (permutation57 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36016step1 raw36016step0; decide +kernel
      have hl : raw36016step1Labels = raw36016step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36016step0 raw36016step0Labels permutation57 permutation2
    mixedMoment B raw36016step1 raw36016step1Labels = mixedMoment B raw36016step2 raw36016step2Labels := by
      have ha : raw36016step2 = -raw36016step1 := by apply Matrix.ext; change ∀ i j, raw36016step2 i j = -(raw36016step1 i j); unfold raw36016step2 raw36016step1; decide +kernel
      have hl : raw36016step2Labels = raw36016step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5229 node5229Labels := by rfl

def raw36017 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -1, -2], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw36017Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36017step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![3, -1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw36017step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36017step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw36017step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36017step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw36017step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36017 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36017 raw36017Labels = mixedMoment B node5228 node5228Labels := by
  calc
    mixedMoment B raw36017 raw36017Labels = mixedMoment B raw36017step0 raw36017step0Labels := by
      have hz : ∀ j, raw36017 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36017step0 = (fun i j => raw36017 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36017step0 raw36017; decide +kernel
      have hl : raw36017step0Labels = raw36017Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36017 raw36017Labels permutation346 hz
    mixedMoment B raw36017step0 raw36017step0Labels = mixedMoment B raw36017step1 raw36017step1Labels := by
      have ha : raw36017step1 = (fun i j => raw36017step0 (permutation56 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36017step1 raw36017step0; decide +kernel
      have hl : raw36017step1Labels = raw36017step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36017step0 raw36017step0Labels permutation56 permutation2
    mixedMoment B raw36017step1 raw36017step1Labels = mixedMoment B raw36017step2 raw36017step2Labels := by
      have ha : raw36017step2 = -raw36017step1 := by apply Matrix.ext; change ∀ i j, raw36017step2 i j = -(raw36017step1 i j); unfold raw36017step2 raw36017step1; decide +kernel
      have hl : raw36017step2Labels = raw36017step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5228 node5228Labels := by rfl

def raw36018 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-3, 4, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw36018Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36018step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-3, 4, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw36018step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36018step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw36018step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw36018step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw36018step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw36018step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw36018step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36018 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36018 raw36018Labels = mixedMoment B node4452 node4452Labels := by
  calc
    mixedMoment B raw36018 raw36018Labels = mixedMoment B raw36018step0 raw36018step0Labels := by
      have hz : ∀ j, raw36018 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36018step0 = (fun i j => raw36018 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36018step0 raw36018; decide +kernel
      have hl : raw36018step0Labels = raw36018Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36018 raw36018Labels permutation346 hz
    mixedMoment B raw36018step0 raw36018step0Labels = mixedMoment B raw36018step1 raw36018step1Labels := by
      have ha : raw36018step1 = (fun i j => raw36018step0 (permutation68 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36018step1 raw36018step0; decide +kernel
      have hl : raw36018step1Labels = raw36018step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36018step0 raw36018step0Labels permutation68 permutation5
    mixedMoment B raw36018step1 raw36018step1Labels = mixedMoment B raw36018step2 raw36018step2Labels := by
      have ha : raw36018step2 = -raw36018step1 := by apply Matrix.ext; change ∀ i j, raw36018step2 i j = -(raw36018step1 i j); unfold raw36018step2 raw36018step1; decide +kernel
      have hl : raw36018step2Labels = raw36018step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36018step2 raw36018step2Labels = mixedMoment B raw36018step3 raw36018step3Labels := by
      have ha : raw36018step3 = raw36018step2 := by apply Matrix.ext; unfold raw36018step3 raw36018step2; decide +kernel
      have hl : raw36018step2Labels = labelEmbedding8 ∘ raw36018step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36018step2 raw36018step2Labels raw36018step3Labels labelEmbedding8 hl
    _ = mixedMoment B node4452 node4452Labels := by rfl

def raw36019 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 3, -1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw36019Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36019step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw36019step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw36019step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw36019step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw36019step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw36019step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36019 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36019 raw36019Labels = mixedMoment B node5070 node5070Labels := by
  calc
    mixedMoment B raw36019 raw36019Labels = mixedMoment B raw36019step0 raw36019step0Labels := by
      have ha : raw36019step0 = (fun i j => raw36019 (permutation299 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36019step0 raw36019; decide +kernel
      have hl : raw36019step0Labels = raw36019Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36019 raw36019Labels permutation299 permutation5
    mixedMoment B raw36019step0 raw36019step0Labels = mixedMoment B raw36019step1 raw36019step1Labels := by
      have ha : raw36019step1 = -raw36019step0 := by apply Matrix.ext; change ∀ i j, raw36019step1 i j = -(raw36019step0 i j); unfold raw36019step1 raw36019step0; decide +kernel
      have hl : raw36019step1Labels = raw36019step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36019step1 raw36019step1Labels = mixedMoment B raw36019step2 raw36019step2Labels := by
      have ha : raw36019step2 = raw36019step1 := by apply Matrix.ext; unfold raw36019step2 raw36019step1; decide +kernel
      have hl : raw36019step1Labels = labelEmbedding8 ∘ raw36019step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36019step1 raw36019step1Labels raw36019step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5070 node5070Labels := by rfl

def raw36020 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw36020Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36020step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 3, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw36020step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36020step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 3, -1], ![1, 0, -1], ![2, -2, 0]]
def raw36020step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36020step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw36020step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw36020step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw36020step3Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw36020step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw36020step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36020 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36020 raw36020Labels = mixedMoment B node5291 node5291Labels := by
  calc
    mixedMoment B raw36020 raw36020Labels = mixedMoment B raw36020step0 raw36020step0Labels := by
      have hz : ∀ j, raw36020 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw36020step0 = (fun i j => raw36020 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw36020step0 raw36020; decide +kernel
      have hl : raw36020step0Labels = raw36020Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36020 raw36020Labels permutation434 hz
    mixedMoment B raw36020step0 raw36020step0Labels = mixedMoment B raw36020step1 raw36020step1Labels := by
      have hz : ∀ j, raw36020step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw36020step1 = (fun i j => raw36020step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw36020step1 raw36020step0; decide +kernel
      have hl : raw36020step1Labels = raw36020step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36020step0 raw36020step0Labels permutation80 hz
    mixedMoment B raw36020step1 raw36020step1Labels = mixedMoment B raw36020step2 raw36020step2Labels := by
      have ha : raw36020step2 = (fun i j => raw36020step1 (permutation16 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36020step2 raw36020step1; decide +kernel
      have hl : raw36020step2Labels = raw36020step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36020step1 raw36020step1Labels permutation16 permutation5
    mixedMoment B raw36020step2 raw36020step2Labels = mixedMoment B raw36020step3 raw36020step3Labels := by
      have ha : raw36020step3 = -raw36020step2 := by apply Matrix.ext; change ∀ i j, raw36020step3 i j = -(raw36020step2 i j); unfold raw36020step3 raw36020step2; decide +kernel
      have hl : raw36020step3Labels = raw36020step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36020step3 raw36020step3Labels = mixedMoment B raw36020step4 raw36020step4Labels := by
      have ha : raw36020step4 = raw36020step3 := by apply Matrix.ext; unfold raw36020step4 raw36020step3; decide +kernel
      have hl : raw36020step3Labels = labelEmbedding8 ∘ raw36020step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36020step3 raw36020step3Labels raw36020step4Labels labelEmbedding8 hl
    _ = mixedMoment B node5291 node5291Labels := by rfl

def raw36021 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 3, -1], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![2, -2, 0]]
def raw36021Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36021step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 3, -1], ![1, -1, 0], ![0, 1, -1], ![2, -2, 0]]
def raw36021step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36021step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw36021step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw36021step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw36021step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw36021step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw36021step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36021 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36021 raw36021Labels = mixedMoment B node5163 node5163Labels := by
  calc
    mixedMoment B raw36021 raw36021Labels = mixedMoment B raw36021step0 raw36021step0Labels := by
      have hz : ∀ j, raw36021 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36021step0 = (fun i j => raw36021 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36021step0 raw36021; decide +kernel
      have hl : raw36021step0Labels = raw36021Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36021 raw36021Labels permutation346 hz
    mixedMoment B raw36021step0 raw36021step0Labels = mixedMoment B raw36021step1 raw36021step1Labels := by
      have ha : raw36021step1 = (fun i j => raw36021step0 (permutation68 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36021step1 raw36021step0; decide +kernel
      have hl : raw36021step1Labels = raw36021step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36021step0 raw36021step0Labels permutation68 permutation5
    mixedMoment B raw36021step1 raw36021step1Labels = mixedMoment B raw36021step2 raw36021step2Labels := by
      have ha : raw36021step2 = -raw36021step1 := by apply Matrix.ext; change ∀ i j, raw36021step2 i j = -(raw36021step1 i j); unfold raw36021step2 raw36021step1; decide +kernel
      have hl : raw36021step2Labels = raw36021step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36021step2 raw36021step2Labels = mixedMoment B raw36021step3 raw36021step3Labels := by
      have ha : raw36021step3 = raw36021step2 := by apply Matrix.ext; unfold raw36021step3 raw36021step2; decide +kernel
      have hl : raw36021step2Labels = labelEmbedding8 ∘ raw36021step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36021step2 raw36021step2Labels raw36021step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5163 node5163Labels := by rfl

def raw36022 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 3, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0]]
def raw36022Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36022step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 3, -1], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0]]
def raw36022step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36022step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw36022step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw36022step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw36022step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw36022step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw36022step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36022 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36022 raw36022Labels = mixedMoment B node5290 node5290Labels := by
  calc
    mixedMoment B raw36022 raw36022Labels = mixedMoment B raw36022step0 raw36022step0Labels := by
      have hz : ∀ j, raw36022 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36022step0 = (fun i j => raw36022 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36022step0 raw36022; decide +kernel
      have hl : raw36022step0Labels = raw36022Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36022 raw36022Labels permutation346 hz
    mixedMoment B raw36022step0 raw36022step0Labels = mixedMoment B raw36022step1 raw36022step1Labels := by
      have ha : raw36022step1 = (fun i j => raw36022step0 (permutation68 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36022step1 raw36022step0; decide +kernel
      have hl : raw36022step1Labels = raw36022step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36022step0 raw36022step0Labels permutation68 permutation5
    mixedMoment B raw36022step1 raw36022step1Labels = mixedMoment B raw36022step2 raw36022step2Labels := by
      have ha : raw36022step2 = -raw36022step1 := by apply Matrix.ext; change ∀ i j, raw36022step2 i j = -(raw36022step1 i j); unfold raw36022step2 raw36022step1; decide +kernel
      have hl : raw36022step2Labels = raw36022step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36022step2 raw36022step2Labels = mixedMoment B raw36022step3 raw36022step3Labels := by
      have ha : raw36022step3 = raw36022step2 := by apply Matrix.ext; unfold raw36022step3 raw36022step2; decide +kernel
      have hl : raw36022step2Labels = labelEmbedding8 ∘ raw36022step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36022step2 raw36022step2Labels raw36022step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5290 node5290Labels := by rfl

def raw36023 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 4, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw36023Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36023step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![0, 2, -2], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw36023step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw36023step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw36023step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw36023step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw36023step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36023 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36023 raw36023Labels = mixedMoment B node4376 node4376Labels := by
  calc
    mixedMoment B raw36023 raw36023Labels = mixedMoment B raw36023step0 raw36023step0Labels := by
      have ha : raw36023step0 = (fun i j => raw36023 (permutation277 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36023step0 raw36023; decide +kernel
      have hl : raw36023step0Labels = raw36023Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36023 raw36023Labels permutation277 permutation5
    mixedMoment B raw36023step0 raw36023step0Labels = mixedMoment B raw36023step1 raw36023step1Labels := by
      have ha : raw36023step1 = -raw36023step0 := by apply Matrix.ext; change ∀ i j, raw36023step1 i j = -(raw36023step0 i j); unfold raw36023step1 raw36023step0; decide +kernel
      have hl : raw36023step1Labels = raw36023step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36023step1 raw36023step1Labels = mixedMoment B raw36023step2 raw36023step2Labels := by
      have ha : raw36023step2 = raw36023step1 := by apply Matrix.ext; unfold raw36023step2 raw36023step1; decide +kernel
      have hl : raw36023step1Labels = labelEmbedding8 ∘ raw36023step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36023step1 raw36023step1Labels raw36023step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4376 node4376Labels := by rfl

def raw36024 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw36024Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36024step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw36024step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36024step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw36024step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw36024step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw36024step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw36024step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw36024step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36024 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36024 raw36024Labels = mixedMoment B node5228 node5228Labels := by
  calc
    mixedMoment B raw36024 raw36024Labels = mixedMoment B raw36024step0 raw36024step0Labels := by
      have hz : ∀ j, raw36024 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw36024step0 = (fun i j => raw36024 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw36024step0 raw36024; decide +kernel
      have hl : raw36024step0Labels = raw36024Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36024 raw36024Labels permutation434 hz
    mixedMoment B raw36024step0 raw36024step0Labels = mixedMoment B raw36024step1 raw36024step1Labels := by
      have ha : raw36024step1 = (fun i j => raw36024step0 (permutation58 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36024step1 raw36024step0; decide +kernel
      have hl : raw36024step1Labels = raw36024step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36024step0 raw36024step0Labels permutation58 permutation5
    mixedMoment B raw36024step1 raw36024step1Labels = mixedMoment B raw36024step2 raw36024step2Labels := by
      have ha : raw36024step2 = -raw36024step1 := by apply Matrix.ext; change ∀ i j, raw36024step2 i j = -(raw36024step1 i j); unfold raw36024step2 raw36024step1; decide +kernel
      have hl : raw36024step2Labels = raw36024step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36024step2 raw36024step2Labels = mixedMoment B raw36024step3 raw36024step3Labels := by
      have ha : raw36024step3 = raw36024step2 := by apply Matrix.ext; unfold raw36024step3 raw36024step2; decide +kernel
      have hl : raw36024step2Labels = labelEmbedding8 ∘ raw36024step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36024step2 raw36024step2Labels raw36024step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5228 node5228Labels := by rfl

def raw36025 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1], ![2, -2, 0]]
def raw36025Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36025step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw36025step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw36025step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw36025step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw36025step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw36025step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36025 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36025 raw36025Labels = mixedMoment B node5123 node5123Labels := by
  calc
    mixedMoment B raw36025 raw36025Labels = mixedMoment B raw36025step0 raw36025step0Labels := by
      have ha : raw36025step0 = (fun i j => raw36025 (permutation322 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36025step0 raw36025; decide +kernel
      have hl : raw36025step0Labels = raw36025Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36025 raw36025Labels permutation322 permutation5
    mixedMoment B raw36025step0 raw36025step0Labels = mixedMoment B raw36025step1 raw36025step1Labels := by
      have ha : raw36025step1 = -raw36025step0 := by apply Matrix.ext; change ∀ i j, raw36025step1 i j = -(raw36025step0 i j); unfold raw36025step1 raw36025step0; decide +kernel
      have hl : raw36025step1Labels = raw36025step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36025step1 raw36025step1Labels = mixedMoment B raw36025step2 raw36025step2Labels := by
      have ha : raw36025step2 = raw36025step1 := by apply Matrix.ext; unfold raw36025step2 raw36025step1; decide +kernel
      have hl : raw36025step1Labels = labelEmbedding8 ∘ raw36025step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36025step1 raw36025step1Labels raw36025step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5123 node5123Labels := by rfl

def raw36026 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0]]
def raw36026Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36026step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw36026step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw36026step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw36026step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw36026step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw36026step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36026 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36026 raw36026Labels = mixedMoment B node5227 node5227Labels := by
  calc
    mixedMoment B raw36026 raw36026Labels = mixedMoment B raw36026step0 raw36026step0Labels := by
      have ha : raw36026step0 = (fun i j => raw36026 (permutation277 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36026step0 raw36026; decide +kernel
      have hl : raw36026step0Labels = raw36026Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36026 raw36026Labels permutation277 permutation5
    mixedMoment B raw36026step0 raw36026step0Labels = mixedMoment B raw36026step1 raw36026step1Labels := by
      have ha : raw36026step1 = -raw36026step0 := by apply Matrix.ext; change ∀ i j, raw36026step1 i j = -(raw36026step0 i j); unfold raw36026step1 raw36026step0; decide +kernel
      have hl : raw36026step1Labels = raw36026step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36026step1 raw36026step1Labels = mixedMoment B raw36026step2 raw36026step2Labels := by
      have ha : raw36026step2 = raw36026step1 := by apply Matrix.ext; unfold raw36026step2 raw36026step1; decide +kernel
      have hl : raw36026step1Labels = labelEmbedding8 ∘ raw36026step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36026step1 raw36026step1Labels raw36026step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5227 node5227Labels := by rfl

def raw36027 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 4, -1], ![0, 0, 0], ![2, -2, 0], ![1, 0, -1], ![2, -2, 0]]
def raw36027Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36027step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 4, -1], ![2, -2, 0], ![1, 0, -1], ![2, -2, 0]]
def raw36027step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36027step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, 2, -2], ![0, -1, 1], ![-2, 0, 2], ![-2, 0, 2]]
def raw36027step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw36027step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -2, 2], ![0, 1, -1], ![2, 0, -2], ![2, 0, -2]]
def raw36027step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw36027step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -2, 2], ![0, 1, -1], ![2, 0, -2], ![2, 0, -2]]
def raw36027step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36027 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36027 raw36027Labels = mixedMoment B node4378 node4378Labels := by
  calc
    mixedMoment B raw36027 raw36027Labels = mixedMoment B raw36027step0 raw36027step0Labels := by
      have hz : ∀ j, raw36027 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36027step0 = (fun i j => raw36027 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36027step0 raw36027; decide +kernel
      have hl : raw36027step0Labels = raw36027Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36027 raw36027Labels permutation346 hz
    mixedMoment B raw36027step0 raw36027step0Labels = mixedMoment B raw36027step1 raw36027step1Labels := by
      have ha : raw36027step1 = (fun i j => raw36027step0 (permutation58 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36027step1 raw36027step0; decide +kernel
      have hl : raw36027step1Labels = raw36027step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36027step0 raw36027step0Labels permutation58 permutation5
    mixedMoment B raw36027step1 raw36027step1Labels = mixedMoment B raw36027step2 raw36027step2Labels := by
      have ha : raw36027step2 = -raw36027step1 := by apply Matrix.ext; change ∀ i j, raw36027step2 i j = -(raw36027step1 i j); unfold raw36027step2 raw36027step1; decide +kernel
      have hl : raw36027step2Labels = raw36027step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36027step2 raw36027step2Labels = mixedMoment B raw36027step3 raw36027step3Labels := by
      have ha : raw36027step3 = raw36027step2 := by apply Matrix.ext; unfold raw36027step3 raw36027step2; decide +kernel
      have hl : raw36027step2Labels = labelEmbedding8 ∘ raw36027step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36027step2 raw36027step2Labels raw36027step3Labels labelEmbedding8 hl
    _ = mixedMoment B node4378 node4378Labels := by rfl

def raw36028 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![-1, 1, 0], ![2, -2, 0], ![1, 0, -1], ![2, -2, 0]]
def raw36028Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36028step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, 2, -2], ![0, -1, 1], ![-2, 0, 2], ![-2, 0, 2]]
def raw36028step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw36028step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -2, 2], ![0, 1, -1], ![2, 0, -2], ![2, 0, -2]]
def raw36028step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw36028step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -2, 2], ![0, 1, -1], ![2, 0, -2], ![2, 0, -2]]
def raw36028step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36028 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36028 raw36028Labels = mixedMoment B node5045 node5045Labels := by
  calc
    mixedMoment B raw36028 raw36028Labels = mixedMoment B raw36028step0 raw36028step0Labels := by
      have ha : raw36028step0 = (fun i j => raw36028 (permutation291 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36028step0 raw36028; decide +kernel
      have hl : raw36028step0Labels = raw36028Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36028 raw36028Labels permutation291 permutation5
    mixedMoment B raw36028step0 raw36028step0Labels = mixedMoment B raw36028step1 raw36028step1Labels := by
      have ha : raw36028step1 = -raw36028step0 := by apply Matrix.ext; change ∀ i j, raw36028step1 i j = -(raw36028step0 i j); unfold raw36028step1 raw36028step0; decide +kernel
      have hl : raw36028step1Labels = raw36028step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36028step1 raw36028step1Labels = mixedMoment B raw36028step2 raw36028step2Labels := by
      have ha : raw36028step2 = raw36028step1 := by apply Matrix.ext; unfold raw36028step2 raw36028step1; decide +kernel
      have hl : raw36028step1Labels = labelEmbedding8 ∘ raw36028step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36028step1 raw36028step1Labels raw36028step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5045 node5045Labels := by rfl

def raw36029 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 0, 0], ![2, -2, 0], ![0, 1, -1], ![2, -2, 0]]
def raw36029Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36029step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![2, -2, 0], ![0, 1, -1], ![2, -2, 0]]
def raw36029step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36029step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 2, -2], ![-2, 0, 2], ![-2, 0, 2]]
def raw36029step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw36029step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![2, 0, -2], ![2, 0, -2]]
def raw36029step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw36029step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![2, 0, -2], ![2, 0, -2]]
def raw36029step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36029 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36029 raw36029Labels = mixedMoment B node5125 node5125Labels := by
  calc
    mixedMoment B raw36029 raw36029Labels = mixedMoment B raw36029step0 raw36029step0Labels := by
      have hz : ∀ j, raw36029 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36029step0 = (fun i j => raw36029 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36029step0 raw36029; decide +kernel
      have hl : raw36029step0Labels = raw36029Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36029 raw36029Labels permutation346 hz
    mixedMoment B raw36029step0 raw36029step0Labels = mixedMoment B raw36029step1 raw36029step1Labels := by
      have ha : raw36029step1 = (fun i j => raw36029step0 (permutation68 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36029step1 raw36029step0; decide +kernel
      have hl : raw36029step1Labels = raw36029step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36029step0 raw36029step0Labels permutation68 permutation5
    mixedMoment B raw36029step1 raw36029step1Labels = mixedMoment B raw36029step2 raw36029step2Labels := by
      have ha : raw36029step2 = -raw36029step1 := by apply Matrix.ext; change ∀ i j, raw36029step2 i j = -(raw36029step1 i j); unfold raw36029step2 raw36029step1; decide +kernel
      have hl : raw36029step2Labels = raw36029step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36029step2 raw36029step2Labels = mixedMoment B raw36029step3 raw36029step3Labels := by
      have ha : raw36029step3 = raw36029step2 := by apply Matrix.ext; unfold raw36029step3 raw36029step2; decide +kernel
      have hl : raw36029step2Labels = labelEmbedding8 ∘ raw36029step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36029step2 raw36029step2Labels raw36029step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5125 node5125Labels := by rfl

def raw36030 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 0, 0], ![2, -2, 0], ![1, 0, -1], ![1, -1, 0]]
def raw36030Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36030step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![2, -2, 0], ![1, 0, -1], ![1, -1, 0]]
def raw36030step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36030step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw36030step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw36030step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw36030step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw36030step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw36030step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36030 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36030 raw36030Labels = mixedMoment B node5228 node5228Labels := by
  calc
    mixedMoment B raw36030 raw36030Labels = mixedMoment B raw36030step0 raw36030step0Labels := by
      have hz : ∀ j, raw36030 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36030step0 = (fun i j => raw36030 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36030step0 raw36030; decide +kernel
      have hl : raw36030step0Labels = raw36030Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36030 raw36030Labels permutation346 hz
    mixedMoment B raw36030step0 raw36030step0Labels = mixedMoment B raw36030step1 raw36030step1Labels := by
      have ha : raw36030step1 = (fun i j => raw36030step0 (permutation59 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36030step1 raw36030step0; decide +kernel
      have hl : raw36030step1Labels = raw36030step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36030step0 raw36030step0Labels permutation59 permutation5
    mixedMoment B raw36030step1 raw36030step1Labels = mixedMoment B raw36030step2 raw36030step2Labels := by
      have ha : raw36030step2 = -raw36030step1 := by apply Matrix.ext; change ∀ i j, raw36030step2 i j = -(raw36030step1 i j); unfold raw36030step2 raw36030step1; decide +kernel
      have hl : raw36030step2Labels = raw36030step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36030step2 raw36030step2Labels = mixedMoment B raw36030step3 raw36030step3Labels := by
      have ha : raw36030step3 = raw36030step2 := by apply Matrix.ext; unfold raw36030step3 raw36030step2; decide +kernel
      have hl : raw36030step2Labels = labelEmbedding8 ∘ raw36030step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36030step2 raw36030step2Labels raw36030step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5228 node5228Labels := by rfl

def raw36031 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 4, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![2, -2, 0]]
def raw36031Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36031step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 4, -1], ![1, -1, 0], ![2, -1, -1], ![2, -2, 0]]
def raw36031step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36031step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, 2, -2], ![-1, 0, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw36031step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw36031step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def raw36031step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw36031step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def raw36031step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36031 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36031 raw36031Labels = mixedMoment B node4381 node4381Labels := by
  calc
    mixedMoment B raw36031 raw36031Labels = mixedMoment B raw36031step0 raw36031step0Labels := by
      have hz : ∀ j, raw36031 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36031step0 = (fun i j => raw36031 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36031step0 raw36031; decide +kernel
      have hl : raw36031step0Labels = raw36031Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36031 raw36031Labels permutation346 hz
    mixedMoment B raw36031step0 raw36031step0Labels = mixedMoment B raw36031step1 raw36031step1Labels := by
      have ha : raw36031step1 = (fun i j => raw36031step0 (permutation56 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36031step1 raw36031step0; decide +kernel
      have hl : raw36031step1Labels = raw36031step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36031step0 raw36031step0Labels permutation56 permutation5
    mixedMoment B raw36031step1 raw36031step1Labels = mixedMoment B raw36031step2 raw36031step2Labels := by
      have ha : raw36031step2 = -raw36031step1 := by apply Matrix.ext; change ∀ i j, raw36031step2 i j = -(raw36031step1 i j); unfold raw36031step2 raw36031step1; decide +kernel
      have hl : raw36031step2Labels = raw36031step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36031step2 raw36031step2Labels = mixedMoment B raw36031step3 raw36031step3Labels := by
      have ha : raw36031step3 = raw36031step2 := by apply Matrix.ext; unfold raw36031step3 raw36031step2; decide +kernel
      have hl : raw36031step2Labels = labelEmbedding8 ∘ raw36031step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36031step2 raw36031step2Labels raw36031step3Labels labelEmbedding8 hl
    _ = mixedMoment B node4381 node4381Labels := by rfl

def raw36032 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, -2, 0]]
def raw36032Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36032step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, 2, -2], ![-1, 0, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw36032step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw36032step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def raw36032step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw36032step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def raw36032step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36032 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36032 raw36032Labels = mixedMoment B node5046 node5046Labels := by
  calc
    mixedMoment B raw36032 raw36032Labels = mixedMoment B raw36032step0 raw36032step0Labels := by
      have ha : raw36032step0 = (fun i j => raw36032 (permutation289 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36032step0 raw36032; decide +kernel
      have hl : raw36032step0Labels = raw36032Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36032 raw36032Labels permutation289 permutation5
    mixedMoment B raw36032step0 raw36032step0Labels = mixedMoment B raw36032step1 raw36032step1Labels := by
      have ha : raw36032step1 = -raw36032step0 := by apply Matrix.ext; change ∀ i j, raw36032step1 i j = -(raw36032step0 i j); unfold raw36032step1 raw36032step0; decide +kernel
      have hl : raw36032step1Labels = raw36032step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36032step1 raw36032step1Labels = mixedMoment B raw36032step2 raw36032step2Labels := by
      have ha : raw36032step2 = raw36032step1 := by apply Matrix.ext; unfold raw36032step2 raw36032step1; decide +kernel
      have hl : raw36032step1Labels = labelEmbedding8 ∘ raw36032step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36032step1 raw36032step1Labels raw36032step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5046 node5046Labels := by rfl

def raw36033 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![2, -2, 0]]
def raw36033Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36033step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 0, 0], ![2, -1, -1], ![2, -2, 0]]
def raw36033step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36033step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![2, -1, -1], ![2, -2, 0]]
def raw36033step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36033step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![-1, -1, 2], ![-2, 0, 2]]
def raw36033step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw36033step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw36033step3Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw36033step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw36033step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36033 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36033 raw36033Labels = mixedMoment B node5238 node5238Labels := by
  calc
    mixedMoment B raw36033 raw36033Labels = mixedMoment B raw36033step0 raw36033step0Labels := by
      have hz : ∀ j, raw36033 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw36033step0 = (fun i j => raw36033 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw36033step0 raw36033; decide +kernel
      have hl : raw36033step0Labels = raw36033Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36033 raw36033Labels permutation434 hz
    mixedMoment B raw36033step0 raw36033step0Labels = mixedMoment B raw36033step1 raw36033step1Labels := by
      have hz : ∀ j, raw36033step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw36033step1 = (fun i j => raw36033step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw36033step1 raw36033step0; decide +kernel
      have hl : raw36033step1Labels = raw36033step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36033step0 raw36033step0Labels permutation80 hz
    mixedMoment B raw36033step1 raw36033step1Labels = mixedMoment B raw36033step2 raw36033step2Labels := by
      have ha : raw36033step2 = (fun i j => raw36033step1 (permutation14 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36033step2 raw36033step1; decide +kernel
      have hl : raw36033step2Labels = raw36033step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36033step1 raw36033step1Labels permutation14 permutation5
    mixedMoment B raw36033step2 raw36033step2Labels = mixedMoment B raw36033step3 raw36033step3Labels := by
      have ha : raw36033step3 = -raw36033step2 := by apply Matrix.ext; change ∀ i j, raw36033step3 i j = -(raw36033step2 i j); unfold raw36033step3 raw36033step2; decide +kernel
      have hl : raw36033step3Labels = raw36033step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36033step3 raw36033step3Labels = mixedMoment B raw36033step4 raw36033step4Labels := by
      have ha : raw36033step4 = raw36033step3 := by apply Matrix.ext; unfold raw36033step4 raw36033step3; decide +kernel
      have hl : raw36033step3Labels = labelEmbedding8 ∘ raw36033step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36033step3 raw36033step3Labels raw36033step4Labels labelEmbedding8 hl
    _ = mixedMoment B node5238 node5238Labels := by rfl

def raw36034 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![1, -1, 0]]
def raw36034Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36034step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![1, -1, 0], ![2, -1, -1], ![1, -1, 0]]
def raw36034step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36034step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw36034step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw36034step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw36034step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw36034step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw36034step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36034 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36034 raw36034Labels = mixedMoment B node5237 node5237Labels := by
  calc
    mixedMoment B raw36034 raw36034Labels = mixedMoment B raw36034step0 raw36034step0Labels := by
      have hz : ∀ j, raw36034 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36034step0 = (fun i j => raw36034 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36034step0 raw36034; decide +kernel
      have hl : raw36034step0Labels = raw36034Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36034 raw36034Labels permutation346 hz
    mixedMoment B raw36034step0 raw36034step0Labels = mixedMoment B raw36034step1 raw36034step1Labels := by
      have ha : raw36034step1 = (fun i j => raw36034step0 (permutation57 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36034step1 raw36034step0; decide +kernel
      have hl : raw36034step1Labels = raw36034step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36034step0 raw36034step0Labels permutation57 permutation5
    mixedMoment B raw36034step1 raw36034step1Labels = mixedMoment B raw36034step2 raw36034step2Labels := by
      have ha : raw36034step2 = -raw36034step1 := by apply Matrix.ext; change ∀ i j, raw36034step2 i j = -(raw36034step1 i j); unfold raw36034step2 raw36034step1; decide +kernel
      have hl : raw36034step2Labels = raw36034step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36034step2 raw36034step2Labels = mixedMoment B raw36034step3 raw36034step3Labels := by
      have ha : raw36034step3 = raw36034step2 := by apply Matrix.ext; unfold raw36034step3 raw36034step2; decide +kernel
      have hl : raw36034step2Labels = labelEmbedding8 ∘ raw36034step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36034step2 raw36034step2Labels raw36034step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5237 node5237Labels := by rfl

def raw36035 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 4, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![3, -3, 0]]
def raw36035Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36035step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 4, -1], ![1, -1, 0], ![1, 0, -1], ![3, -3, 0]]
def raw36035step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36035step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, 2, -2], ![0, -1, 1], ![-1, 0, 1], ![-3, 0, 3]]
def raw36035step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw36035step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![3, 0, -3]]
def raw36035step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw36035step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![3, 0, -3]]
def raw36035step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36035 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36035 raw36035Labels = mixedMoment B node4377 node4377Labels := by
  calc
    mixedMoment B raw36035 raw36035Labels = mixedMoment B raw36035step0 raw36035step0Labels := by
      have hz : ∀ j, raw36035 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36035step0 = (fun i j => raw36035 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36035step0 raw36035; decide +kernel
      have hl : raw36035step0Labels = raw36035Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36035 raw36035Labels permutation346 hz
    mixedMoment B raw36035step0 raw36035step0Labels = mixedMoment B raw36035step1 raw36035step1Labels := by
      have ha : raw36035step1 = (fun i j => raw36035step0 (permutation58 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36035step1 raw36035step0; decide +kernel
      have hl : raw36035step1Labels = raw36035step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36035step0 raw36035step0Labels permutation58 permutation5
    mixedMoment B raw36035step1 raw36035step1Labels = mixedMoment B raw36035step2 raw36035step2Labels := by
      have ha : raw36035step2 = -raw36035step1 := by apply Matrix.ext; change ∀ i j, raw36035step2 i j = -(raw36035step1 i j); unfold raw36035step2 raw36035step1; decide +kernel
      have hl : raw36035step2Labels = raw36035step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36035step2 raw36035step2Labels = mixedMoment B raw36035step3 raw36035step3Labels := by
      have ha : raw36035step3 = raw36035step2 := by apply Matrix.ext; unfold raw36035step3 raw36035step2; decide +kernel
      have hl : raw36035step2Labels = labelEmbedding8 ∘ raw36035step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36035step2 raw36035step2Labels raw36035step3Labels labelEmbedding8 hl
    _ = mixedMoment B node4377 node4377Labels := by rfl

def raw36036 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -3, 0]]
def raw36036Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36036step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, 2, 0], ![-2, -1, 3]]
def raw36036step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36036step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def raw36036step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36036step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def raw36036step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36036 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36036 raw36036Labels = mixedMoment B node4714 node4714Labels := by
  calc
    mixedMoment B raw36036 raw36036Labels = mixedMoment B raw36036step0 raw36036step0Labels := by
      have ha : raw36036step0 = (fun i j => raw36036 (permutation663 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36036step0 raw36036; decide +kernel
      have hl : raw36036step0Labels = raw36036Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36036 raw36036Labels permutation663 permutation3
    mixedMoment B raw36036step0 raw36036step0Labels = mixedMoment B raw36036step1 raw36036step1Labels := by
      have ha : raw36036step1 = -raw36036step0 := by apply Matrix.ext; change ∀ i j, raw36036step1 i j = -(raw36036step0 i j); unfold raw36036step1 raw36036step0; decide +kernel
      have hl : raw36036step1Labels = raw36036step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36036step1 raw36036step1Labels = mixedMoment B raw36036step2 raw36036step2Labels := by
      have ha : raw36036step2 = raw36036step1 := by apply Matrix.ext; unfold raw36036step2 raw36036step1; decide +kernel
      have hl : raw36036step1Labels = labelEmbedding6 ∘ raw36036step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36036step1 raw36036step1Labels raw36036step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4714 node4714Labels := by rfl

def raw36037 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![3, -3, 0]]
def raw36037Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36037step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![1, -1, 0], ![0, 1, -1], ![3, -3, 0]]
def raw36037step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36037step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, -1, 3]]
def raw36037step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36037step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw36037step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36037step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw36037step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36037 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36037 raw36037Labels = mixedMoment B node4744 node4744Labels := by
  calc
    mixedMoment B raw36037 raw36037Labels = mixedMoment B raw36037step0 raw36037step0Labels := by
      have hz : ∀ j, raw36037 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36037step0 = (fun i j => raw36037 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36037step0 raw36037; decide +kernel
      have hl : raw36037step0Labels = raw36037Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36037 raw36037Labels permutation346 hz
    mixedMoment B raw36037step0 raw36037step0Labels = mixedMoment B raw36037step1 raw36037step1Labels := by
      have ha : raw36037step1 = (fun i j => raw36037step0 (permutation144 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36037step1 raw36037step0; decide +kernel
      have hl : raw36037step1Labels = raw36037step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36037step0 raw36037step0Labels permutation144 permutation3
    mixedMoment B raw36037step1 raw36037step1Labels = mixedMoment B raw36037step2 raw36037step2Labels := by
      have ha : raw36037step2 = -raw36037step1 := by apply Matrix.ext; change ∀ i j, raw36037step2 i j = -(raw36037step1 i j); unfold raw36037step2 raw36037step1; decide +kernel
      have hl : raw36037step2Labels = raw36037step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36037step2 raw36037step2Labels = mixedMoment B raw36037step3 raw36037step3Labels := by
      have ha : raw36037step3 = raw36037step2 := by apply Matrix.ext; unfold raw36037step3 raw36037step2; decide +kernel
      have hl : raw36037step2Labels = labelEmbedding6 ∘ raw36037step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36037step2 raw36037step2Labels raw36037step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4744 node4744Labels := by rfl

def raw36038 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-3, 0, 3], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36038Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36038step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-3, 0, 3], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36038step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36038step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw36038step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36038 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36038 raw36038Labels = mixedMoment B node4834 node4834Labels := by
  calc
    mixedMoment B raw36038 raw36038Labels = mixedMoment B raw36038step0 raw36038step0Labels := by
      have hz : ∀ j, raw36038 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36038step0 = (fun i j => raw36038 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36038step0 raw36038; decide +kernel
      have hl : raw36038step0Labels = raw36038Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36038 raw36038Labels permutation346 hz
    mixedMoment B raw36038step0 raw36038step0Labels = mixedMoment B raw36038step1 raw36038step1Labels := by
      have ha : raw36038step1 = (fun i j => raw36038step0 (permutation58 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36038step1 raw36038step0; decide +kernel
      have hl : raw36038step1Labels = raw36038step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36038step0 raw36038step0Labels permutation58 permutation2
    _ = mixedMoment B node4834 node4834Labels := by rfl

def raw36039 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36039Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36039step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw36039step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36039step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw36039step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36039step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw36039step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36039 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36039 raw36039Labels = mixedMoment B node5241 node5241Labels := by
  calc
    mixedMoment B raw36039 raw36039Labels = mixedMoment B raw36039step0 raw36039step0Labels := by
      have ha : raw36039step0 = (fun i j => raw36039 (permutation267 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36039step0 raw36039; decide +kernel
      have hl : raw36039step0Labels = raw36039Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36039 raw36039Labels permutation267 permutation7
    mixedMoment B raw36039step0 raw36039step0Labels = mixedMoment B raw36039step1 raw36039step1Labels := by
      have ha : raw36039step1 = -raw36039step0 := by apply Matrix.ext; change ∀ i j, raw36039step1 i j = -(raw36039step0 i j); unfold raw36039step1 raw36039step0; decide +kernel
      have hl : raw36039step1Labels = raw36039step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36039step1 raw36039step1Labels = mixedMoment B raw36039step2 raw36039step2Labels := by
      have ha : raw36039step2 = raw36039step1 := by apply Matrix.ext; unfold raw36039step2 raw36039step1; decide +kernel
      have hl : raw36039step1Labels = labelEmbedding10 ∘ raw36039step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36039step1 raw36039step1Labels raw36039step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5241 node5241Labels := by rfl

def raw36040 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36040Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36040step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36040step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36040step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw36040step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36040step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36040step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36040step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36040step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36040 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36040 raw36040Labels = mixedMoment B node5258 node5258Labels := by
  calc
    mixedMoment B raw36040 raw36040Labels = mixedMoment B raw36040step0 raw36040step0Labels := by
      have hz : ∀ j, raw36040 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36040step0 = (fun i j => raw36040 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36040step0 raw36040; decide +kernel
      have hl : raw36040step0Labels = raw36040Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36040 raw36040Labels permutation346 hz
    mixedMoment B raw36040step0 raw36040step0Labels = mixedMoment B raw36040step1 raw36040step1Labels := by
      have ha : raw36040step1 = (fun i j => raw36040step0 (permutation58 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36040step1 raw36040step0; decide +kernel
      have hl : raw36040step1Labels = raw36040step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36040step0 raw36040step0Labels permutation58 permutation7
    mixedMoment B raw36040step1 raw36040step1Labels = mixedMoment B raw36040step2 raw36040step2Labels := by
      have ha : raw36040step2 = -raw36040step1 := by apply Matrix.ext; change ∀ i j, raw36040step2 i j = -(raw36040step1 i j); unfold raw36040step2 raw36040step1; decide +kernel
      have hl : raw36040step2Labels = raw36040step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36040step2 raw36040step2Labels = mixedMoment B raw36040step3 raw36040step3Labels := by
      have ha : raw36040step3 = raw36040step2 := by apply Matrix.ext; unfold raw36040step3 raw36040step2; decide +kernel
      have hl : raw36040step2Labels = labelEmbedding10 ∘ raw36040step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36040step2 raw36040step2Labels raw36040step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5258 node5258Labels := by rfl

def raw36041 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![0, 0, 0], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2]]
def raw36041Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36041step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![0, 0, 0], ![1, 0, -1], ![2, 0, -2]]
def raw36041step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36041step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![1, 0, -1], ![2, 0, -2]]
def raw36041step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36041step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw36041step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36041step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw36041step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36041step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw36041step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36041 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36041 raw36041Labels = mixedMoment B node5274 node5274Labels := by
  calc
    mixedMoment B raw36041 raw36041Labels = mixedMoment B raw36041step0 raw36041step0Labels := by
      have hz : ∀ j, raw36041 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw36041step0 = (fun i j => raw36041 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw36041step0 raw36041; decide +kernel
      have hl : raw36041step0Labels = raw36041Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36041 raw36041Labels permutation520 hz
    mixedMoment B raw36041step0 raw36041step0Labels = mixedMoment B raw36041step1 raw36041step1Labels := by
      have hz : ∀ j, raw36041step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw36041step1 = (fun i j => raw36041step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw36041step1 raw36041step0; decide +kernel
      have hl : raw36041step1Labels = raw36041step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36041step0 raw36041step0Labels permutation80 hz
    mixedMoment B raw36041step1 raw36041step1Labels = mixedMoment B raw36041step2 raw36041step2Labels := by
      have ha : raw36041step2 = (fun i j => raw36041step1 (permutation14 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36041step2 raw36041step1; decide +kernel
      have hl : raw36041step2Labels = raw36041step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36041step1 raw36041step1Labels permutation14 permutation7
    mixedMoment B raw36041step2 raw36041step2Labels = mixedMoment B raw36041step3 raw36041step3Labels := by
      have ha : raw36041step3 = -raw36041step2 := by apply Matrix.ext; change ∀ i j, raw36041step3 i j = -(raw36041step2 i j); unfold raw36041step3 raw36041step2; decide +kernel
      have hl : raw36041step3Labels = raw36041step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36041step3 raw36041step3Labels = mixedMoment B raw36041step4 raw36041step4Labels := by
      have ha : raw36041step4 = raw36041step3 := by apply Matrix.ext; unfold raw36041step4 raw36041step3; decide +kernel
      have hl : raw36041step3Labels = labelEmbedding10 ∘ raw36041step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36041step3 raw36041step3Labels raw36041step4Labels labelEmbedding10 hl
    _ = mixedMoment B node5274 node5274Labels := by rfl

def raw36042 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw36042Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36042step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw36042step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36042step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw36042step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36042step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36042step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36042step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36042step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36042 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36042 raw36042Labels = mixedMoment B node5259 node5259Labels := by
  calc
    mixedMoment B raw36042 raw36042Labels = mixedMoment B raw36042step0 raw36042step0Labels := by
      have hz : ∀ j, raw36042 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36042step0 = (fun i j => raw36042 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36042step0 raw36042; decide +kernel
      have hl : raw36042step0Labels = raw36042Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36042 raw36042Labels permutation346 hz
    mixedMoment B raw36042step0 raw36042step0Labels = mixedMoment B raw36042step1 raw36042step1Labels := by
      have ha : raw36042step1 = (fun i j => raw36042step0 (permutation58 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36042step1 raw36042step0; decide +kernel
      have hl : raw36042step1Labels = raw36042step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36042step0 raw36042step0Labels permutation58 permutation7
    mixedMoment B raw36042step1 raw36042step1Labels = mixedMoment B raw36042step2 raw36042step2Labels := by
      have ha : raw36042step2 = -raw36042step1 := by apply Matrix.ext; change ∀ i j, raw36042step2 i j = -(raw36042step1 i j); unfold raw36042step2 raw36042step1; decide +kernel
      have hl : raw36042step2Labels = raw36042step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36042step2 raw36042step2Labels = mixedMoment B raw36042step3 raw36042step3Labels := by
      have ha : raw36042step3 = raw36042step2 := by apply Matrix.ext; unfold raw36042step3 raw36042step2; decide +kernel
      have hl : raw36042step2Labels = labelEmbedding10 ∘ raw36042step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36042step2 raw36042step2Labels raw36042step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5259 node5259Labels := by rfl

def raw36043 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36043Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36043step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36043step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36043step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw36043step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36043step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw36043step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36043 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36043 raw36043Labels = mixedMoment B node4880 node4880Labels := by
  calc
    mixedMoment B raw36043 raw36043Labels = mixedMoment B raw36043step0 raw36043step0Labels := by
      have hz : ∀ j, raw36043 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36043step0 = (fun i j => raw36043 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36043step0 raw36043; decide +kernel
      have hl : raw36043step0Labels = raw36043Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36043 raw36043Labels permutation346 hz
    mixedMoment B raw36043step0 raw36043step0Labels = mixedMoment B raw36043step1 raw36043step1Labels := by
      have ha : raw36043step1 = (fun i j => raw36043step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36043step1 raw36043step0; decide +kernel
      have hl : raw36043step1Labels = raw36043step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36043step0 raw36043step0Labels permutation32 permutation3
    mixedMoment B raw36043step1 raw36043step1Labels = mixedMoment B raw36043step2 raw36043step2Labels := by
      have ha : raw36043step2 = raw36043step1 := by apply Matrix.ext; unfold raw36043step2 raw36043step1; decide +kernel
      have hl : raw36043step1Labels = labelEmbedding6 ∘ raw36043step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36043step1 raw36043step1Labels raw36043step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4880 node4880Labels := by rfl

def raw36044 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36044Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36044step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw36044step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw36044step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw36044step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw36044step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw36044step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36044 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36044 raw36044Labels = mixedMoment B node5254 node5254Labels := by
  calc
    mixedMoment B raw36044 raw36044Labels = mixedMoment B raw36044step0 raw36044step0Labels := by
      have ha : raw36044step0 = (fun i j => raw36044 (permutation326 i) (permutation6 j)) := by apply Matrix.ext; unfold raw36044step0 raw36044; decide +kernel
      have hl : raw36044step0Labels = raw36044Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36044 raw36044Labels permutation326 permutation6
    mixedMoment B raw36044step0 raw36044step0Labels = mixedMoment B raw36044step1 raw36044step1Labels := by
      have ha : raw36044step1 = -raw36044step0 := by apply Matrix.ext; change ∀ i j, raw36044step1 i j = -(raw36044step0 i j); unfold raw36044step1 raw36044step0; decide +kernel
      have hl : raw36044step1Labels = raw36044step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36044step1 raw36044step1Labels = mixedMoment B raw36044step2 raw36044step2Labels := by
      have ha : raw36044step2 = raw36044step1 := by apply Matrix.ext; unfold raw36044step2 raw36044step1; decide +kernel
      have hl : raw36044step1Labels = labelEmbedding9 ∘ raw36044step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36044step1 raw36044step1Labels raw36044step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5254 node5254Labels := by rfl

def raw36045 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36045Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36045step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36045step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36045step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw36045step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw36045step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw36045step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw36045step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw36045step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36045 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36045 raw36045Labels = mixedMoment B node5267 node5267Labels := by
  calc
    mixedMoment B raw36045 raw36045Labels = mixedMoment B raw36045step0 raw36045step0Labels := by
      have hz : ∀ j, raw36045 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36045step0 = (fun i j => raw36045 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36045step0 raw36045; decide +kernel
      have hl : raw36045step0Labels = raw36045Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36045 raw36045Labels permutation346 hz
    mixedMoment B raw36045step0 raw36045step0Labels = mixedMoment B raw36045step1 raw36045step1Labels := by
      have ha : raw36045step1 = (fun i j => raw36045step0 (permutation68 i) (permutation6 j)) := by apply Matrix.ext; unfold raw36045step1 raw36045step0; decide +kernel
      have hl : raw36045step1Labels = raw36045step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36045step0 raw36045step0Labels permutation68 permutation6
    mixedMoment B raw36045step1 raw36045step1Labels = mixedMoment B raw36045step2 raw36045step2Labels := by
      have ha : raw36045step2 = -raw36045step1 := by apply Matrix.ext; change ∀ i j, raw36045step2 i j = -(raw36045step1 i j); unfold raw36045step2 raw36045step1; decide +kernel
      have hl : raw36045step2Labels = raw36045step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36045step2 raw36045step2Labels = mixedMoment B raw36045step3 raw36045step3Labels := by
      have ha : raw36045step3 = raw36045step2 := by apply Matrix.ext; unfold raw36045step3 raw36045step2; decide +kernel
      have hl : raw36045step2Labels = labelEmbedding9 ∘ raw36045step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36045step2 raw36045step2Labels raw36045step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5267 node5267Labels := by rfl

def raw36046 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![0, 0, 0], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2]]
def raw36046Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36046step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![0, 0, 0], ![1, 0, -1], ![2, 0, -2]]
def raw36046step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36046step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![1, 0, -1], ![2, 0, -2]]
def raw36046step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36046step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw36046step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw36046step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw36046step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw36046step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw36046step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36046 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36046 raw36046Labels = mixedMoment B node5302 node5302Labels := by
  calc
    mixedMoment B raw36046 raw36046Labels = mixedMoment B raw36046step0 raw36046step0Labels := by
      have hz : ∀ j, raw36046 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw36046step0 = (fun i j => raw36046 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw36046step0 raw36046; decide +kernel
      have hl : raw36046step0Labels = raw36046Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36046 raw36046Labels permutation520 hz
    mixedMoment B raw36046step0 raw36046step0Labels = mixedMoment B raw36046step1 raw36046step1Labels := by
      have hz : ∀ j, raw36046step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw36046step1 = (fun i j => raw36046step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw36046step1 raw36046step0; decide +kernel
      have hl : raw36046step1Labels = raw36046step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36046step0 raw36046step0Labels permutation80 hz
    mixedMoment B raw36046step1 raw36046step1Labels = mixedMoment B raw36046step2 raw36046step2Labels := by
      have ha : raw36046step2 = (fun i j => raw36046step1 (permutation14 i) (permutation6 j)) := by apply Matrix.ext; unfold raw36046step2 raw36046step1; decide +kernel
      have hl : raw36046step2Labels = raw36046step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36046step1 raw36046step1Labels permutation14 permutation6
    mixedMoment B raw36046step2 raw36046step2Labels = mixedMoment B raw36046step3 raw36046step3Labels := by
      have ha : raw36046step3 = -raw36046step2 := by apply Matrix.ext; change ∀ i j, raw36046step3 i j = -(raw36046step2 i j); unfold raw36046step3 raw36046step2; decide +kernel
      have hl : raw36046step3Labels = raw36046step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36046step3 raw36046step3Labels = mixedMoment B raw36046step4 raw36046step4Labels := by
      have ha : raw36046step4 = raw36046step3 := by apply Matrix.ext; unfold raw36046step4 raw36046step3; decide +kernel
      have hl : raw36046step3Labels = labelEmbedding9 ∘ raw36046step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36046step3 raw36046step3Labels raw36046step4Labels labelEmbedding9 hl
    _ = mixedMoment B node5302 node5302Labels := by rfl

def raw36047 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw36047Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36047step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw36047step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36047step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw36047step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw36047step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw36047step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw36047step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw36047step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36047 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36047 raw36047Labels = mixedMoment B node5266 node5266Labels := by
  calc
    mixedMoment B raw36047 raw36047Labels = mixedMoment B raw36047step0 raw36047step0Labels := by
      have hz : ∀ j, raw36047 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36047step0 = (fun i j => raw36047 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36047step0 raw36047; decide +kernel
      have hl : raw36047step0Labels = raw36047Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36047 raw36047Labels permutation346 hz
    mixedMoment B raw36047step0 raw36047step0Labels = mixedMoment B raw36047step1 raw36047step1Labels := by
      have ha : raw36047step1 = (fun i j => raw36047step0 (permutation68 i) (permutation6 j)) := by apply Matrix.ext; unfold raw36047step1 raw36047step0; decide +kernel
      have hl : raw36047step1Labels = raw36047step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36047step0 raw36047step0Labels permutation68 permutation6
    mixedMoment B raw36047step1 raw36047step1Labels = mixedMoment B raw36047step2 raw36047step2Labels := by
      have ha : raw36047step2 = -raw36047step1 := by apply Matrix.ext; change ∀ i j, raw36047step2 i j = -(raw36047step1 i j); unfold raw36047step2 raw36047step1; decide +kernel
      have hl : raw36047step2Labels = raw36047step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36047step2 raw36047step2Labels = mixedMoment B raw36047step3 raw36047step3Labels := by
      have ha : raw36047step3 = raw36047step2 := by apply Matrix.ext; unfold raw36047step3 raw36047step2; decide +kernel
      have hl : raw36047step2Labels = labelEmbedding9 ∘ raw36047step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36047step2 raw36047step2Labels raw36047step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5266 node5266Labels := by rfl

def raw36048 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36048Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36048step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw36048step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36048step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw36048step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36048 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36048 raw36048Labels = mixedMoment B node4698 node4698Labels := by
  calc
    mixedMoment B raw36048 raw36048Labels = mixedMoment B raw36048step0 raw36048step0Labels := by
      have ha : raw36048step0 = (fun i j => raw36048 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36048step0 raw36048; decide +kernel
      have hl : raw36048step0Labels = raw36048Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36048 raw36048Labels permutation158 permutation3
    mixedMoment B raw36048step0 raw36048step0Labels = mixedMoment B raw36048step1 raw36048step1Labels := by
      have ha : raw36048step1 = raw36048step0 := by apply Matrix.ext; unfold raw36048step1 raw36048step0; decide +kernel
      have hl : raw36048step0Labels = labelEmbedding6 ∘ raw36048step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36048step0 raw36048step0Labels raw36048step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4698 node4698Labels := by rfl

def raw36049 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 0, 3], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36049Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36049step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw36049step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36049 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36049 raw36049Labels = mixedMoment B node4676 node4676Labels := by
  calc
    mixedMoment B raw36049 raw36049Labels = mixedMoment B raw36049step0 raw36049step0Labels := by
      have ha : raw36049step0 = (fun i j => raw36049 (permutation267 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36049step0 raw36049; decide +kernel
      have hl : raw36049step0Labels = raw36049Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36049 raw36049Labels permutation267 permutation2
    _ = mixedMoment B node4676 node4676Labels := by rfl

def raw36050 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36050Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36050step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw36050step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36050step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36050step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36050step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36050step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36050 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36050 raw36050Labels = mixedMoment B node5219 node5219Labels := by
  calc
    mixedMoment B raw36050 raw36050Labels = mixedMoment B raw36050step0 raw36050step0Labels := by
      have ha : raw36050step0 = (fun i j => raw36050 (permutation267 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36050step0 raw36050; decide +kernel
      have hl : raw36050step0Labels = raw36050Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36050 raw36050Labels permutation267 permutation7
    mixedMoment B raw36050step0 raw36050step0Labels = mixedMoment B raw36050step1 raw36050step1Labels := by
      have ha : raw36050step1 = -raw36050step0 := by apply Matrix.ext; change ∀ i j, raw36050step1 i j = -(raw36050step0 i j); unfold raw36050step1 raw36050step0; decide +kernel
      have hl : raw36050step1Labels = raw36050step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36050step1 raw36050step1Labels = mixedMoment B raw36050step2 raw36050step2Labels := by
      have ha : raw36050step2 = raw36050step1 := by apply Matrix.ext; unfold raw36050step2 raw36050step1; decide +kernel
      have hl : raw36050step1Labels = labelEmbedding10 ∘ raw36050step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36050step1 raw36050step1Labels raw36050step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5219 node5219Labels := by rfl

def raw36051 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![1, -1, 0], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2]]
def raw36051Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36051step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw36051step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36051step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw36051step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36051step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw36051step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36051step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw36051step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36051 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36051 raw36051Labels = mixedMoment B node5228 node5228Labels := by
  calc
    mixedMoment B raw36051 raw36051Labels = mixedMoment B raw36051step0 raw36051step0Labels := by
      have hz : ∀ j, raw36051 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw36051step0 = (fun i j => raw36051 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw36051step0 raw36051; decide +kernel
      have hl : raw36051step0Labels = raw36051Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36051 raw36051Labels permutation520 hz
    mixedMoment B raw36051step0 raw36051step0Labels = mixedMoment B raw36051step1 raw36051step1Labels := by
      have ha : raw36051step1 = (fun i j => raw36051step0 (permutation56 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36051step1 raw36051step0; decide +kernel
      have hl : raw36051step1Labels = raw36051step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36051step0 raw36051step0Labels permutation56 permutation7
    mixedMoment B raw36051step1 raw36051step1Labels = mixedMoment B raw36051step2 raw36051step2Labels := by
      have ha : raw36051step2 = -raw36051step1 := by apply Matrix.ext; change ∀ i j, raw36051step2 i j = -(raw36051step1 i j); unfold raw36051step2 raw36051step1; decide +kernel
      have hl : raw36051step2Labels = raw36051step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36051step2 raw36051step2Labels = mixedMoment B raw36051step3 raw36051step3Labels := by
      have ha : raw36051step3 = raw36051step2 := by apply Matrix.ext; unfold raw36051step3 raw36051step2; decide +kernel
      have hl : raw36051step2Labels = labelEmbedding10 ∘ raw36051step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36051step2 raw36051step2Labels raw36051step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5228 node5228Labels := by rfl

def raw36052 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw36052Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36052step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw36052step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36052step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36052step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36052step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36052step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36052 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36052 raw36052Labels = mixedMoment B node5220 node5220Labels := by
  calc
    mixedMoment B raw36052 raw36052Labels = mixedMoment B raw36052step0 raw36052step0Labels := by
      have ha : raw36052step0 = (fun i j => raw36052 (permutation267 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36052step0 raw36052; decide +kernel
      have hl : raw36052step0Labels = raw36052Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36052 raw36052Labels permutation267 permutation7
    mixedMoment B raw36052step0 raw36052step0Labels = mixedMoment B raw36052step1 raw36052step1Labels := by
      have ha : raw36052step1 = -raw36052step0 := by apply Matrix.ext; change ∀ i j, raw36052step1 i j = -(raw36052step0 i j); unfold raw36052step1 raw36052step0; decide +kernel
      have hl : raw36052step1Labels = raw36052step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36052step1 raw36052step1Labels = mixedMoment B raw36052step2 raw36052step2Labels := by
      have ha : raw36052step2 = raw36052step1 := by apply Matrix.ext; unfold raw36052step2 raw36052step1; decide +kernel
      have hl : raw36052step1Labels = labelEmbedding10 ∘ raw36052step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36052step1 raw36052step1Labels raw36052step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5220 node5220Labels := by rfl

def raw36053 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![0, 0, 0], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36053Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36053step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36053step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36053step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw36053step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36053step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw36053step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36053 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36053 raw36053Labels = mixedMoment B node4703 node4703Labels := by
  calc
    mixedMoment B raw36053 raw36053Labels = mixedMoment B raw36053step0 raw36053step0Labels := by
      have hz : ∀ j, raw36053 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36053step0 = (fun i j => raw36053 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36053step0 raw36053; decide +kernel
      have hl : raw36053step0Labels = raw36053Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36053 raw36053Labels permutation346 hz
    mixedMoment B raw36053step0 raw36053step0Labels = mixedMoment B raw36053step1 raw36053step1Labels := by
      have ha : raw36053step1 = (fun i j => raw36053step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36053step1 raw36053step0; decide +kernel
      have hl : raw36053step1Labels = raw36053step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36053step0 raw36053step0Labels permutation35 permutation3
    mixedMoment B raw36053step1 raw36053step1Labels = mixedMoment B raw36053step2 raw36053step2Labels := by
      have ha : raw36053step2 = raw36053step1 := by apply Matrix.ext; unfold raw36053step2 raw36053step1; decide +kernel
      have hl : raw36053step1Labels = labelEmbedding6 ∘ raw36053step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36053step1 raw36053step1Labels raw36053step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4703 node4703Labels := by rfl

def raw36054 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 0, 3], ![0, 0, 0], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36054Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36054step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 0, 3], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36054step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36054step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw36054step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36054 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36054 raw36054Labels = mixedMoment B node4684 node4684Labels := by
  calc
    mixedMoment B raw36054 raw36054Labels = mixedMoment B raw36054step0 raw36054step0Labels := by
      have hz : ∀ j, raw36054 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36054step0 = (fun i j => raw36054 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36054step0 raw36054; decide +kernel
      have hl : raw36054step0Labels = raw36054Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36054 raw36054Labels permutation346 hz
    mixedMoment B raw36054step0 raw36054step0Labels = mixedMoment B raw36054step1 raw36054step1Labels := by
      have ha : raw36054step1 = (fun i j => raw36054step0 (permutation58 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36054step1 raw36054step0; decide +kernel
      have hl : raw36054step1Labels = raw36054step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36054step0 raw36054step0Labels permutation58 permutation2
    _ = mixedMoment B node4684 node4684Labels := by rfl

def raw36055 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![-1, 1, 0], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36055Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36055step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw36055step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36055step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw36055step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36055step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw36055step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36055 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36055 raw36055Labels = mixedMoment B node5215 node5215Labels := by
  calc
    mixedMoment B raw36055 raw36055Labels = mixedMoment B raw36055step0 raw36055step0Labels := by
      have ha : raw36055step0 = (fun i j => raw36055 (permutation267 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36055step0 raw36055; decide +kernel
      have hl : raw36055step0Labels = raw36055Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36055 raw36055Labels permutation267 permutation7
    mixedMoment B raw36055step0 raw36055step0Labels = mixedMoment B raw36055step1 raw36055step1Labels := by
      have ha : raw36055step1 = -raw36055step0 := by apply Matrix.ext; change ∀ i j, raw36055step1 i j = -(raw36055step0 i j); unfold raw36055step1 raw36055step0; decide +kernel
      have hl : raw36055step1Labels = raw36055step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36055step1 raw36055step1Labels = mixedMoment B raw36055step2 raw36055step2Labels := by
      have ha : raw36055step2 = raw36055step1 := by apply Matrix.ext; unfold raw36055step2 raw36055step1; decide +kernel
      have hl : raw36055step1Labels = labelEmbedding10 ∘ raw36055step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36055step1 raw36055step1Labels raw36055step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5215 node5215Labels := by rfl

def raw36056 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![0, 0, 0], ![2, -1, -1], ![0, 0, 0], ![2, 0, -2]]
def raw36056Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36056step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![0, 0, 0], ![2, -1, -1], ![2, 0, -2]]
def raw36056step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36056step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![2, -1, -1], ![2, 0, -2]]
def raw36056step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36056step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![-1, -1, 2], ![-2, 0, 2]]
def raw36056step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36056step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw36056step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36056step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw36056step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36056 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36056 raw36056Labels = mixedMoment B node5238 node5238Labels := by
  calc
    mixedMoment B raw36056 raw36056Labels = mixedMoment B raw36056step0 raw36056step0Labels := by
      have hz : ∀ j, raw36056 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw36056step0 = (fun i j => raw36056 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw36056step0 raw36056; decide +kernel
      have hl : raw36056step0Labels = raw36056Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36056 raw36056Labels permutation520 hz
    mixedMoment B raw36056step0 raw36056step0Labels = mixedMoment B raw36056step1 raw36056step1Labels := by
      have hz : ∀ j, raw36056step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw36056step1 = (fun i j => raw36056step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw36056step1 raw36056step0; decide +kernel
      have hl : raw36056step1Labels = raw36056step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36056step0 raw36056step0Labels permutation80 hz
    mixedMoment B raw36056step1 raw36056step1Labels = mixedMoment B raw36056step2 raw36056step2Labels := by
      have ha : raw36056step2 = (fun i j => raw36056step1 (permutation14 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36056step2 raw36056step1; decide +kernel
      have hl : raw36056step2Labels = raw36056step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36056step1 raw36056step1Labels permutation14 permutation7
    mixedMoment B raw36056step2 raw36056step2Labels = mixedMoment B raw36056step3 raw36056step3Labels := by
      have ha : raw36056step3 = -raw36056step2 := by apply Matrix.ext; change ∀ i j, raw36056step3 i j = -(raw36056step2 i j); unfold raw36056step3 raw36056step2; decide +kernel
      have hl : raw36056step3Labels = raw36056step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36056step3 raw36056step3Labels = mixedMoment B raw36056step4 raw36056step4Labels := by
      have ha : raw36056step4 = raw36056step3 := by apply Matrix.ext; unfold raw36056step4 raw36056step3; decide +kernel
      have hl : raw36056step3Labels = labelEmbedding10 ∘ raw36056step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36056step3 raw36056step3Labels raw36056step4Labels labelEmbedding10 hl
    _ = mixedMoment B node5238 node5238Labels := by rfl

def raw36057 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![0, 0, 0], ![2, -1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw36057Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36057step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![2, -1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw36057step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36057step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw36057step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36057step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw36057step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36057step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw36057step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36057 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36057 raw36057Labels = mixedMoment B node5229 node5229Labels := by
  calc
    mixedMoment B raw36057 raw36057Labels = mixedMoment B raw36057step0 raw36057step0Labels := by
      have hz : ∀ j, raw36057 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36057step0 = (fun i j => raw36057 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36057step0 raw36057; decide +kernel
      have hl : raw36057step0Labels = raw36057Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36057 raw36057Labels permutation346 hz
    mixedMoment B raw36057step0 raw36057step0Labels = mixedMoment B raw36057step1 raw36057step1Labels := by
      have ha : raw36057step1 = (fun i j => raw36057step0 (permutation58 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36057step1 raw36057step0; decide +kernel
      have hl : raw36057step1Labels = raw36057step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36057step0 raw36057step0Labels permutation58 permutation7
    mixedMoment B raw36057step1 raw36057step1Labels = mixedMoment B raw36057step2 raw36057step2Labels := by
      have ha : raw36057step2 = -raw36057step1 := by apply Matrix.ext; change ∀ i j, raw36057step2 i j = -(raw36057step1 i j); unfold raw36057step2 raw36057step1; decide +kernel
      have hl : raw36057step2Labels = raw36057step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36057step2 raw36057step2Labels = mixedMoment B raw36057step3 raw36057step3Labels := by
      have ha : raw36057step3 = raw36057step2 := by apply Matrix.ext; unfold raw36057step3 raw36057step2; decide +kernel
      have hl : raw36057step2Labels = labelEmbedding10 ∘ raw36057step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36057step2 raw36057step2Labels raw36057step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5229 node5229Labels := by rfl

def raw36058 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw36058Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36058step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw36058step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36058step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw36058step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36058step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw36058step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36058 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36058 raw36058Labels = mixedMoment B node4700 node4700Labels := by
  calc
    mixedMoment B raw36058 raw36058Labels = mixedMoment B raw36058step0 raw36058step0Labels := by
      have hz : ∀ j, raw36058 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36058step0 = (fun i j => raw36058 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36058step0 raw36058; decide +kernel
      have hl : raw36058step0Labels = raw36058Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36058 raw36058Labels permutation346 hz
    mixedMoment B raw36058step0 raw36058step0Labels = mixedMoment B raw36058step1 raw36058step1Labels := by
      have ha : raw36058step1 = (fun i j => raw36058step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36058step1 raw36058step0; decide +kernel
      have hl : raw36058step1Labels = raw36058step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36058step0 raw36058step0Labels permutation33 permutation3
    mixedMoment B raw36058step1 raw36058step1Labels = mixedMoment B raw36058step2 raw36058step2Labels := by
      have ha : raw36058step2 = raw36058step1 := by apply Matrix.ext; unfold raw36058step2 raw36058step1; decide +kernel
      have hl : raw36058step1Labels = labelEmbedding6 ∘ raw36058step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36058step1 raw36058step1Labels raw36058step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4700 node4700Labels := by rfl

def raw36059 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 0, 3], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw36059Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36059step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 0, 3], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw36059step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36059step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw36059step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36059 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36059 raw36059Labels = mixedMoment B node4688 node4688Labels := by
  calc
    mixedMoment B raw36059 raw36059Labels = mixedMoment B raw36059step0 raw36059step0Labels := by
      have hz : ∀ j, raw36059 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36059step0 = (fun i j => raw36059 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36059step0 raw36059; decide +kernel
      have hl : raw36059step0Labels = raw36059Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36059 raw36059Labels permutation346 hz
    mixedMoment B raw36059step0 raw36059step0Labels = mixedMoment B raw36059step1 raw36059step1Labels := by
      have ha : raw36059step1 = (fun i j => raw36059step0 (permutation56 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36059step1 raw36059step0; decide +kernel
      have hl : raw36059step1Labels = raw36059step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36059step0 raw36059step0Labels permutation56 permutation2
    _ = mixedMoment B node4688 node4688Labels := by rfl

def raw36060 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw36060Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36060step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 0, 2]]
def raw36060step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36060step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw36060step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36060step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw36060step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36060 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36060 raw36060Labels = mixedMoment B node5216 node5216Labels := by
  calc
    mixedMoment B raw36060 raw36060Labels = mixedMoment B raw36060step0 raw36060step0Labels := by
      have ha : raw36060step0 = (fun i j => raw36060 (permutation267 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36060step0 raw36060; decide +kernel
      have hl : raw36060step0Labels = raw36060Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36060 raw36060Labels permutation267 permutation7
    mixedMoment B raw36060step0 raw36060step0Labels = mixedMoment B raw36060step1 raw36060step1Labels := by
      have ha : raw36060step1 = -raw36060step0 := by apply Matrix.ext; change ∀ i j, raw36060step1 i j = -(raw36060step0 i j); unfold raw36060step1 raw36060step0; decide +kernel
      have hl : raw36060step1Labels = raw36060step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36060step1 raw36060step1Labels = mixedMoment B raw36060step2 raw36060step2Labels := by
      have ha : raw36060step2 = raw36060step1 := by apply Matrix.ext; unfold raw36060step2 raw36060step1; decide +kernel
      have hl : raw36060step1Labels = labelEmbedding10 ∘ raw36060step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36060step1 raw36060step1Labels raw36060step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5216 node5216Labels := by rfl

def raw36061 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw36061Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36061step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw36061step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36061step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw36061step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36061step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw36061step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36061step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw36061step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36061 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36061 raw36061Labels = mixedMoment B node5232 node5232Labels := by
  calc
    mixedMoment B raw36061 raw36061Labels = mixedMoment B raw36061step0 raw36061step0Labels := by
      have hz : ∀ j, raw36061 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36061step0 = (fun i j => raw36061 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36061step0 raw36061; decide +kernel
      have hl : raw36061step0Labels = raw36061Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36061 raw36061Labels permutation346 hz
    mixedMoment B raw36061step0 raw36061step0Labels = mixedMoment B raw36061step1 raw36061step1Labels := by
      have ha : raw36061step1 = (fun i j => raw36061step0 (permutation58 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36061step1 raw36061step0; decide +kernel
      have hl : raw36061step1Labels = raw36061step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36061step0 raw36061step0Labels permutation58 permutation7
    mixedMoment B raw36061step1 raw36061step1Labels = mixedMoment B raw36061step2 raw36061step2Labels := by
      have ha : raw36061step2 = -raw36061step1 := by apply Matrix.ext; change ∀ i j, raw36061step2 i j = -(raw36061step1 i j); unfold raw36061step2 raw36061step1; decide +kernel
      have hl : raw36061step2Labels = raw36061step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36061step2 raw36061step2Labels = mixedMoment B raw36061step3 raw36061step3Labels := by
      have ha : raw36061step3 = raw36061step2 := by apply Matrix.ext; unfold raw36061step3 raw36061step2; decide +kernel
      have hl : raw36061step2Labels = labelEmbedding10 ∘ raw36061step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36061step2 raw36061step2Labels raw36061step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5232 node5232Labels := by rfl

def raw36062 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![1, 1, -2]]
def raw36062Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36062step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![1, 0, -1], ![2, -2, 0], ![1, 1, -2]]
def raw36062step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36062step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw36062step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36062step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw36062step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36062step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw36062step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36062 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36062 raw36062Labels = mixedMoment B node5233 node5233Labels := by
  calc
    mixedMoment B raw36062 raw36062Labels = mixedMoment B raw36062step0 raw36062step0Labels := by
      have hz : ∀ j, raw36062 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36062step0 = (fun i j => raw36062 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36062step0 raw36062; decide +kernel
      have hl : raw36062step0Labels = raw36062Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36062 raw36062Labels permutation346 hz
    mixedMoment B raw36062step0 raw36062step0Labels = mixedMoment B raw36062step1 raw36062step1Labels := by
      have ha : raw36062step1 = (fun i j => raw36062step0 (permutation58 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36062step1 raw36062step0; decide +kernel
      have hl : raw36062step1Labels = raw36062step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36062step0 raw36062step0Labels permutation58 permutation7
    mixedMoment B raw36062step1 raw36062step1Labels = mixedMoment B raw36062step2 raw36062step2Labels := by
      have ha : raw36062step2 = -raw36062step1 := by apply Matrix.ext; change ∀ i j, raw36062step2 i j = -(raw36062step1 i j); unfold raw36062step2 raw36062step1; decide +kernel
      have hl : raw36062step2Labels = raw36062step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36062step2 raw36062step2Labels = mixedMoment B raw36062step3 raw36062step3Labels := by
      have ha : raw36062step3 = raw36062step2 := by apply Matrix.ext; unfold raw36062step3 raw36062step2; decide +kernel
      have hl : raw36062step2Labels = labelEmbedding10 ∘ raw36062step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36062step2 raw36062step2Labels raw36062step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5233 node5233Labels := by rfl

def raw36063 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw36063Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36063step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw36063step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36063step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw36063step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36063step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw36063step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36063 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36063 raw36063Labels = mixedMoment B node4699 node4699Labels := by
  calc
    mixedMoment B raw36063 raw36063Labels = mixedMoment B raw36063step0 raw36063step0Labels := by
      have hz : ∀ j, raw36063 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36063step0 = (fun i j => raw36063 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36063step0 raw36063; decide +kernel
      have hl : raw36063step0Labels = raw36063Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36063 raw36063Labels permutation346 hz
    mixedMoment B raw36063step0 raw36063step0Labels = mixedMoment B raw36063step1 raw36063step1Labels := by
      have ha : raw36063step1 = (fun i j => raw36063step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36063step1 raw36063step0; decide +kernel
      have hl : raw36063step1Labels = raw36063step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36063step0 raw36063step0Labels permutation32 permutation3
    mixedMoment B raw36063step1 raw36063step1Labels = mixedMoment B raw36063step2 raw36063step2Labels := by
      have ha : raw36063step2 = raw36063step1 := by apply Matrix.ext; unfold raw36063step2 raw36063step1; decide +kernel
      have hl : raw36063step1Labels = labelEmbedding6 ∘ raw36063step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36063step1 raw36063step1Labels raw36063step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4699 node4699Labels := by rfl

def raw36064 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 0, 3], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw36064Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36064step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 0, 3], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw36064step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36064step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw36064step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36064 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36064 raw36064Labels = mixedMoment B node4681 node4681Labels := by
  calc
    mixedMoment B raw36064 raw36064Labels = mixedMoment B raw36064step0 raw36064step0Labels := by
      have hz : ∀ j, raw36064 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36064step0 = (fun i j => raw36064 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36064step0 raw36064; decide +kernel
      have hl : raw36064step0Labels = raw36064Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36064 raw36064Labels permutation346 hz
    mixedMoment B raw36064step0 raw36064step0Labels = mixedMoment B raw36064step1 raw36064step1Labels := by
      have ha : raw36064step1 = (fun i j => raw36064step0 (permutation58 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36064step1 raw36064step0; decide +kernel
      have hl : raw36064step1Labels = raw36064step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36064step0 raw36064step0Labels permutation58 permutation2
    _ = mixedMoment B node4681 node4681Labels := by rfl

def raw36065 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw36065Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36065step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 1, 0], ![-2, 2, 0], ![-2, -1, 3]]
def raw36065step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36065step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw36065step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36065 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36065 raw36065Labels = mixedMoment B node5035 node5035Labels := by
  calc
    mixedMoment B raw36065 raw36065Labels = mixedMoment B raw36065step0 raw36065step0Labels := by
      have ha : raw36065step0 = (fun i j => raw36065 (permutation663 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36065step0 raw36065; decide +kernel
      have hl : raw36065step0Labels = raw36065Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36065 raw36065Labels permutation663 permutation2
    mixedMoment B raw36065step0 raw36065step0Labels = mixedMoment B raw36065step1 raw36065step1Labels := by
      have ha : raw36065step1 = -raw36065step0 := by apply Matrix.ext; change ∀ i j, raw36065step1 i j = -(raw36065step0 i j); unfold raw36065step1 raw36065step0; decide +kernel
      have hl : raw36065step1Labels = raw36065step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5035 node5035Labels := by rfl

def raw36066 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw36066Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36066step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw36066step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36066step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 1, -1], ![-2, 2, 0], ![-2, -1, 3]]
def raw36066step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36066step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw36066step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36066 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36066 raw36066Labels = mixedMoment B node5140 node5140Labels := by
  calc
    mixedMoment B raw36066 raw36066Labels = mixedMoment B raw36066step0 raw36066step0Labels := by
      have hz : ∀ j, raw36066 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36066step0 = (fun i j => raw36066 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36066step0 raw36066; decide +kernel
      have hl : raw36066step0Labels = raw36066Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36066 raw36066Labels permutation346 hz
    mixedMoment B raw36066step0 raw36066step0Labels = mixedMoment B raw36066step1 raw36066step1Labels := by
      have ha : raw36066step1 = (fun i j => raw36066step0 (permutation150 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36066step1 raw36066step0; decide +kernel
      have hl : raw36066step1Labels = raw36066step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36066step0 raw36066step0Labels permutation150 permutation2
    mixedMoment B raw36066step1 raw36066step1Labels = mixedMoment B raw36066step2 raw36066step2Labels := by
      have ha : raw36066step2 = -raw36066step1 := by apply Matrix.ext; change ∀ i j, raw36066step2 i j = -(raw36066step1 i j); unfold raw36066step2 raw36066step1; decide +kernel
      have hl : raw36066step2Labels = raw36066step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5140 node5140Labels := by rfl

def raw36067 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![0, 0, 0], ![1, 0, -1], ![0, 0, 0], ![3, -1, -2]]
def raw36067Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36067step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw36067step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36067step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![1, 0, -1], ![3, -1, -2]]
def raw36067step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36067step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![-2, 2, 0], ![-2, -1, 3]]
def raw36067step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36067step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw36067step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36067 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36067 raw36067Labels = mixedMoment B node5110 node5110Labels := by
  calc
    mixedMoment B raw36067 raw36067Labels = mixedMoment B raw36067step0 raw36067step0Labels := by
      have hz : ∀ j, raw36067 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw36067step0 = (fun i j => raw36067 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw36067step0 raw36067; decide +kernel
      have hl : raw36067step0Labels = raw36067Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36067 raw36067Labels permutation520 hz
    mixedMoment B raw36067step0 raw36067step0Labels = mixedMoment B raw36067step1 raw36067step1Labels := by
      have hz : ∀ j, raw36067step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw36067step1 = (fun i j => raw36067step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw36067step1 raw36067step0; decide +kernel
      have hl : raw36067step1Labels = raw36067step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36067step0 raw36067step0Labels permutation80 hz
    mixedMoment B raw36067step1 raw36067step1Labels = mixedMoment B raw36067step2 raw36067step2Labels := by
      have ha : raw36067step2 = (fun i j => raw36067step1 (permutation30 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36067step2 raw36067step1; decide +kernel
      have hl : raw36067step2Labels = raw36067step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36067step1 raw36067step1Labels permutation30 permutation2
    mixedMoment B raw36067step2 raw36067step2Labels = mixedMoment B raw36067step3 raw36067step3Labels := by
      have ha : raw36067step3 = -raw36067step2 := by apply Matrix.ext; change ∀ i j, raw36067step3 i j = -(raw36067step2 i j); unfold raw36067step3 raw36067step2; decide +kernel
      have hl : raw36067step3Labels = raw36067step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5110 node5110Labels := by rfl

def raw36068 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-3, 0, 3], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36068Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36068step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-3, 0, 3], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36068step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36068step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw36068step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36068step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw36068step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36068step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw36068step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36068 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36068 raw36068Labels = mixedMoment B node2205 node2205Labels := by
  calc
    mixedMoment B raw36068 raw36068Labels = mixedMoment B raw36068step0 raw36068step0Labels := by
      have hz : ∀ j, raw36068 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36068step0 = (fun i j => raw36068 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36068step0 raw36068; decide +kernel
      have hl : raw36068step0Labels = raw36068Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36068 raw36068Labels permutation346 hz
    mixedMoment B raw36068step0 raw36068step0Labels = mixedMoment B raw36068step1 raw36068step1Labels := by
      have ha : raw36068step1 = (fun i j => raw36068step0 (permutation58 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36068step1 raw36068step0; decide +kernel
      have hl : raw36068step1Labels = raw36068step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36068step0 raw36068step0Labels permutation58 permutation7
    mixedMoment B raw36068step1 raw36068step1Labels = mixedMoment B raw36068step2 raw36068step2Labels := by
      have ha : raw36068step2 = -raw36068step1 := by apply Matrix.ext; change ∀ i j, raw36068step2 i j = -(raw36068step1 i j); unfold raw36068step2 raw36068step1; decide +kernel
      have hl : raw36068step2Labels = raw36068step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36068step2 raw36068step2Labels = mixedMoment B raw36068step3 raw36068step3Labels := by
      have ha : raw36068step3 = raw36068step2 := by apply Matrix.ext; unfold raw36068step3 raw36068step2; decide +kernel
      have hl : raw36068step2Labels = labelEmbedding1 ∘ raw36068step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36068step2 raw36068step2Labels raw36068step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2205 node2205Labels := by rfl

def raw36069 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36069Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36069step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw36069step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36069step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw36069step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36069step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw36069step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36069 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36069 raw36069Labels = mixedMoment B node2694 node2694Labels := by
  calc
    mixedMoment B raw36069 raw36069Labels = mixedMoment B raw36069step0 raw36069step0Labels := by
      have ha : raw36069step0 = (fun i j => raw36069 (permutation267 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36069step0 raw36069; decide +kernel
      have hl : raw36069step0Labels = raw36069Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36069 raw36069Labels permutation267 permutation7
    mixedMoment B raw36069step0 raw36069step0Labels = mixedMoment B raw36069step1 raw36069step1Labels := by
      have ha : raw36069step1 = -raw36069step0 := by apply Matrix.ext; change ∀ i j, raw36069step1 i j = -(raw36069step0 i j); unfold raw36069step1 raw36069step0; decide +kernel
      have hl : raw36069step1Labels = raw36069step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36069step1 raw36069step1Labels = mixedMoment B raw36069step2 raw36069step2Labels := by
      have ha : raw36069step2 = raw36069step1 := by apply Matrix.ext; unfold raw36069step2 raw36069step1; decide +kernel
      have hl : raw36069step1Labels = labelEmbedding1 ∘ raw36069step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36069step1 raw36069step1Labels raw36069step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2694 node2694Labels := by rfl

def raw36070 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36070Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36070step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36070step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36070step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw36070step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36070step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36070step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36070step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36070step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36070 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36070 raw36070Labels = mixedMoment B node2722 node2722Labels := by
  calc
    mixedMoment B raw36070 raw36070Labels = mixedMoment B raw36070step0 raw36070step0Labels := by
      have hz : ∀ j, raw36070 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36070step0 = (fun i j => raw36070 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36070step0 raw36070; decide +kernel
      have hl : raw36070step0Labels = raw36070Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36070 raw36070Labels permutation346 hz
    mixedMoment B raw36070step0 raw36070step0Labels = mixedMoment B raw36070step1 raw36070step1Labels := by
      have ha : raw36070step1 = (fun i j => raw36070step0 (permutation58 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36070step1 raw36070step0; decide +kernel
      have hl : raw36070step1Labels = raw36070step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36070step0 raw36070step0Labels permutation58 permutation7
    mixedMoment B raw36070step1 raw36070step1Labels = mixedMoment B raw36070step2 raw36070step2Labels := by
      have ha : raw36070step2 = -raw36070step1 := by apply Matrix.ext; change ∀ i j, raw36070step2 i j = -(raw36070step1 i j); unfold raw36070step2 raw36070step1; decide +kernel
      have hl : raw36070step2Labels = raw36070step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36070step2 raw36070step2Labels = mixedMoment B raw36070step3 raw36070step3Labels := by
      have ha : raw36070step3 = raw36070step2 := by apply Matrix.ext; unfold raw36070step3 raw36070step2; decide +kernel
      have hl : raw36070step2Labels = labelEmbedding1 ∘ raw36070step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36070step2 raw36070step2Labels raw36070step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2722 node2722Labels := by rfl

def raw36071 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![0, 0, 0], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2]]
def raw36071Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36071step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![0, 0, 0], ![1, 0, -1], ![2, 0, -2]]
def raw36071step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36071step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![1, 0, -1], ![2, 0, -2]]
def raw36071step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36071step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw36071step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36071step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw36071step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36071step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw36071step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36071 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36071 raw36071Labels = mixedMoment B node2742 node2742Labels := by
  calc
    mixedMoment B raw36071 raw36071Labels = mixedMoment B raw36071step0 raw36071step0Labels := by
      have hz : ∀ j, raw36071 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw36071step0 = (fun i j => raw36071 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw36071step0 raw36071; decide +kernel
      have hl : raw36071step0Labels = raw36071Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36071 raw36071Labels permutation520 hz
    mixedMoment B raw36071step0 raw36071step0Labels = mixedMoment B raw36071step1 raw36071step1Labels := by
      have hz : ∀ j, raw36071step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw36071step1 = (fun i j => raw36071step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw36071step1 raw36071step0; decide +kernel
      have hl : raw36071step1Labels = raw36071step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36071step0 raw36071step0Labels permutation80 hz
    mixedMoment B raw36071step1 raw36071step1Labels = mixedMoment B raw36071step2 raw36071step2Labels := by
      have ha : raw36071step2 = (fun i j => raw36071step1 (permutation14 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36071step2 raw36071step1; decide +kernel
      have hl : raw36071step2Labels = raw36071step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36071step1 raw36071step1Labels permutation14 permutation7
    mixedMoment B raw36071step2 raw36071step2Labels = mixedMoment B raw36071step3 raw36071step3Labels := by
      have ha : raw36071step3 = -raw36071step2 := by apply Matrix.ext; change ∀ i j, raw36071step3 i j = -(raw36071step2 i j); unfold raw36071step3 raw36071step2; decide +kernel
      have hl : raw36071step3Labels = raw36071step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36071step3 raw36071step3Labels = mixedMoment B raw36071step4 raw36071step4Labels := by
      have ha : raw36071step4 = raw36071step3 := by apply Matrix.ext; unfold raw36071step4 raw36071step3; decide +kernel
      have hl : raw36071step3Labels = labelEmbedding1 ∘ raw36071step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36071step3 raw36071step3Labels raw36071step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2742 node2742Labels := by rfl

def raw36072 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw36072Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36072step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw36072step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36072step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw36072step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36072step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36072step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36072step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36072step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36072 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36072 raw36072Labels = mixedMoment B node2723 node2723Labels := by
  calc
    mixedMoment B raw36072 raw36072Labels = mixedMoment B raw36072step0 raw36072step0Labels := by
      have hz : ∀ j, raw36072 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36072step0 = (fun i j => raw36072 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36072step0 raw36072; decide +kernel
      have hl : raw36072step0Labels = raw36072Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36072 raw36072Labels permutation346 hz
    mixedMoment B raw36072step0 raw36072step0Labels = mixedMoment B raw36072step1 raw36072step1Labels := by
      have ha : raw36072step1 = (fun i j => raw36072step0 (permutation58 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36072step1 raw36072step0; decide +kernel
      have hl : raw36072step1Labels = raw36072step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36072step0 raw36072step0Labels permutation58 permutation7
    mixedMoment B raw36072step1 raw36072step1Labels = mixedMoment B raw36072step2 raw36072step2Labels := by
      have ha : raw36072step2 = -raw36072step1 := by apply Matrix.ext; change ∀ i j, raw36072step2 i j = -(raw36072step1 i j); unfold raw36072step2 raw36072step1; decide +kernel
      have hl : raw36072step2Labels = raw36072step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36072step2 raw36072step2Labels = mixedMoment B raw36072step3 raw36072step3Labels := by
      have ha : raw36072step3 = raw36072step2 := by apply Matrix.ext; unfold raw36072step3 raw36072step2; decide +kernel
      have hl : raw36072step2Labels = labelEmbedding1 ∘ raw36072step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36072step2 raw36072step2Labels raw36072step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2723 node2723Labels := by rfl

def raw36073 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36073Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36073step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36073step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36073step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 3, -1]]
def raw36073step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36073step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw36073step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36073step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw36073step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36073 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36073 raw36073Labels = mixedMoment B node2254 node2254Labels := by
  calc
    mixedMoment B raw36073 raw36073Labels = mixedMoment B raw36073step0 raw36073step0Labels := by
      have hz : ∀ j, raw36073 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36073step0 = (fun i j => raw36073 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36073step0 raw36073; decide +kernel
      have hl : raw36073step0Labels = raw36073Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36073 raw36073Labels permutation346 hz
    mixedMoment B raw36073step0 raw36073step0Labels = mixedMoment B raw36073step1 raw36073step1Labels := by
      have ha : raw36073step1 = (fun i j => raw36073step0 (permutation43 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36073step1 raw36073step0; decide +kernel
      have hl : raw36073step1Labels = raw36073step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36073step0 raw36073step0Labels permutation43 permutation5
    mixedMoment B raw36073step1 raw36073step1Labels = mixedMoment B raw36073step2 raw36073step2Labels := by
      have ha : raw36073step2 = -raw36073step1 := by apply Matrix.ext; change ∀ i j, raw36073step2 i j = -(raw36073step1 i j); unfold raw36073step2 raw36073step1; decide +kernel
      have hl : raw36073step2Labels = raw36073step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36073step2 raw36073step2Labels = mixedMoment B raw36073step3 raw36073step3Labels := by
      have ha : raw36073step3 = raw36073step2 := by apply Matrix.ext; unfold raw36073step3 raw36073step2; decide +kernel
      have hl : raw36073step2Labels = labelEmbedding1 ∘ raw36073step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36073step2 raw36073step2Labels raw36073step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2254 node2254Labels := by rfl

def raw36074 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36074Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36074step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw36074step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36074step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw36074step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36074step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw36074step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36074 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36074 raw36074Labels = mixedMoment B node3016 node3016Labels := by
  calc
    mixedMoment B raw36074 raw36074Labels = mixedMoment B raw36074step0 raw36074step0Labels := by
      have ha : raw36074step0 = (fun i j => raw36074 (permutation267 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36074step0 raw36074; decide +kernel
      have hl : raw36074step0Labels = raw36074Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36074 raw36074Labels permutation267 permutation7
    mixedMoment B raw36074step0 raw36074step0Labels = mixedMoment B raw36074step1 raw36074step1Labels := by
      have ha : raw36074step1 = -raw36074step0 := by apply Matrix.ext; change ∀ i j, raw36074step1 i j = -(raw36074step0 i j); unfold raw36074step1 raw36074step0; decide +kernel
      have hl : raw36074step1Labels = raw36074step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36074step1 raw36074step1Labels = mixedMoment B raw36074step2 raw36074step2Labels := by
      have ha : raw36074step2 = raw36074step1 := by apply Matrix.ext; unfold raw36074step2 raw36074step1; decide +kernel
      have hl : raw36074step1Labels = labelEmbedding1 ∘ raw36074step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36074step1 raw36074step1Labels raw36074step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3016 node3016Labels := by rfl

def raw36075 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36075Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36075step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36075step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36075step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw36075step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36075step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36075step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36075step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36075step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36075 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36075 raw36075Labels = mixedMoment B node3038 node3038Labels := by
  calc
    mixedMoment B raw36075 raw36075Labels = mixedMoment B raw36075step0 raw36075step0Labels := by
      have hz : ∀ j, raw36075 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36075step0 = (fun i j => raw36075 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36075step0 raw36075; decide +kernel
      have hl : raw36075step0Labels = raw36075Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36075 raw36075Labels permutation346 hz
    mixedMoment B raw36075step0 raw36075step0Labels = mixedMoment B raw36075step1 raw36075step1Labels := by
      have ha : raw36075step1 = (fun i j => raw36075step0 (permutation58 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36075step1 raw36075step0; decide +kernel
      have hl : raw36075step1Labels = raw36075step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36075step0 raw36075step0Labels permutation58 permutation7
    mixedMoment B raw36075step1 raw36075step1Labels = mixedMoment B raw36075step2 raw36075step2Labels := by
      have ha : raw36075step2 = -raw36075step1 := by apply Matrix.ext; change ∀ i j, raw36075step2 i j = -(raw36075step1 i j); unfold raw36075step2 raw36075step1; decide +kernel
      have hl : raw36075step2Labels = raw36075step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36075step2 raw36075step2Labels = mixedMoment B raw36075step3 raw36075step3Labels := by
      have ha : raw36075step3 = raw36075step2 := by apply Matrix.ext; unfold raw36075step3 raw36075step2; decide +kernel
      have hl : raw36075step2Labels = labelEmbedding1 ∘ raw36075step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36075step2 raw36075step2Labels raw36075step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3038 node3038Labels := by rfl

def raw36076 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![0, 0, 0], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2]]
def raw36076Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36076step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![0, 0, 0], ![1, 0, -1], ![2, 0, -2]]
def raw36076step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36076step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![1, 0, -1], ![2, 0, -2]]
def raw36076step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36076step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![-1, 0, 1], ![-2, 0, 2]]
def raw36076step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36076step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw36076step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36076step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw36076step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36076 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36076 raw36076Labels = mixedMoment B node3054 node3054Labels := by
  calc
    mixedMoment B raw36076 raw36076Labels = mixedMoment B raw36076step0 raw36076step0Labels := by
      have hz : ∀ j, raw36076 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw36076step0 = (fun i j => raw36076 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw36076step0 raw36076; decide +kernel
      have hl : raw36076step0Labels = raw36076Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36076 raw36076Labels permutation520 hz
    mixedMoment B raw36076step0 raw36076step0Labels = mixedMoment B raw36076step1 raw36076step1Labels := by
      have hz : ∀ j, raw36076step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw36076step1 = (fun i j => raw36076step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw36076step1 raw36076step0; decide +kernel
      have hl : raw36076step1Labels = raw36076step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36076step0 raw36076step0Labels permutation80 hz
    mixedMoment B raw36076step1 raw36076step1Labels = mixedMoment B raw36076step2 raw36076step2Labels := by
      have ha : raw36076step2 = (fun i j => raw36076step1 (permutation14 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36076step2 raw36076step1; decide +kernel
      have hl : raw36076step2Labels = raw36076step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36076step1 raw36076step1Labels permutation14 permutation7
    mixedMoment B raw36076step2 raw36076step2Labels = mixedMoment B raw36076step3 raw36076step3Labels := by
      have ha : raw36076step3 = -raw36076step2 := by apply Matrix.ext; change ∀ i j, raw36076step3 i j = -(raw36076step2 i j); unfold raw36076step3 raw36076step2; decide +kernel
      have hl : raw36076step3Labels = raw36076step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36076step3 raw36076step3Labels = mixedMoment B raw36076step4 raw36076step4Labels := by
      have ha : raw36076step4 = raw36076step3 := by apply Matrix.ext; unfold raw36076step4 raw36076step3; decide +kernel
      have hl : raw36076step3Labels = labelEmbedding1 ∘ raw36076step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36076step3 raw36076step3Labels raw36076step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3054 node3054Labels := by rfl

def raw36077 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw36077Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36077step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw36077step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36077step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw36077step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36077step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36077step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36077step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36077step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36077 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36077 raw36077Labels = mixedMoment B node3039 node3039Labels := by
  calc
    mixedMoment B raw36077 raw36077Labels = mixedMoment B raw36077step0 raw36077step0Labels := by
      have hz : ∀ j, raw36077 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36077step0 = (fun i j => raw36077 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36077step0 raw36077; decide +kernel
      have hl : raw36077step0Labels = raw36077Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36077 raw36077Labels permutation346 hz
    mixedMoment B raw36077step0 raw36077step0Labels = mixedMoment B raw36077step1 raw36077step1Labels := by
      have ha : raw36077step1 = (fun i j => raw36077step0 (permutation58 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36077step1 raw36077step0; decide +kernel
      have hl : raw36077step1Labels = raw36077step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36077step0 raw36077step0Labels permutation58 permutation7
    mixedMoment B raw36077step1 raw36077step1Labels = mixedMoment B raw36077step2 raw36077step2Labels := by
      have ha : raw36077step2 = -raw36077step1 := by apply Matrix.ext; change ∀ i j, raw36077step2 i j = -(raw36077step1 i j); unfold raw36077step2 raw36077step1; decide +kernel
      have hl : raw36077step2Labels = raw36077step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36077step2 raw36077step2Labels = mixedMoment B raw36077step3 raw36077step3Labels := by
      have ha : raw36077step3 = raw36077step2 := by apply Matrix.ext; unfold raw36077step3 raw36077step2; decide +kernel
      have hl : raw36077step2Labels = labelEmbedding1 ∘ raw36077step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36077step2 raw36077step2Labels raw36077step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3039 node3039Labels := by rfl

def raw36078 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36078Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36078step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 3, -2], ![-1, 0, 1], ![-1, 0, 1]]
def raw36078step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36078step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1]]
def raw36078step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36078step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1]]
def raw36078step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36078 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36078 raw36078Labels = mixedMoment B node2248 node2248Labels := by
  calc
    mixedMoment B raw36078 raw36078Labels = mixedMoment B raw36078step0 raw36078step0Labels := by
      have ha : raw36078step0 = (fun i j => raw36078 (permutation218 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36078step0 raw36078; decide +kernel
      have hl : raw36078step0Labels = raw36078Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36078 raw36078Labels permutation218 permutation5
    mixedMoment B raw36078step0 raw36078step0Labels = mixedMoment B raw36078step1 raw36078step1Labels := by
      have ha : raw36078step1 = -raw36078step0 := by apply Matrix.ext; change ∀ i j, raw36078step1 i j = -(raw36078step0 i j); unfold raw36078step1 raw36078step0; decide +kernel
      have hl : raw36078step1Labels = raw36078step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36078step1 raw36078step1Labels = mixedMoment B raw36078step2 raw36078step2Labels := by
      have ha : raw36078step2 = raw36078step1 := by apply Matrix.ext; unfold raw36078step2 raw36078step1; decide +kernel
      have hl : raw36078step1Labels = labelEmbedding1 ∘ raw36078step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36078step1 raw36078step1Labels raw36078step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2248 node2248Labels := by rfl

def raw36079 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 0, 3], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36079Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36079step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw36079step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36079step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw36079step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36079step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw36079step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36079 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36079 raw36079Labels = mixedMoment B node2141 node2141Labels := by
  calc
    mixedMoment B raw36079 raw36079Labels = mixedMoment B raw36079step0 raw36079step0Labels := by
      have ha : raw36079step0 = (fun i j => raw36079 (permutation267 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36079step0 raw36079; decide +kernel
      have hl : raw36079step0Labels = raw36079Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36079 raw36079Labels permutation267 permutation7
    mixedMoment B raw36079step0 raw36079step0Labels = mixedMoment B raw36079step1 raw36079step1Labels := by
      have ha : raw36079step1 = -raw36079step0 := by apply Matrix.ext; change ∀ i j, raw36079step1 i j = -(raw36079step0 i j); unfold raw36079step1 raw36079step0; decide +kernel
      have hl : raw36079step1Labels = raw36079step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36079step1 raw36079step1Labels = mixedMoment B raw36079step2 raw36079step2Labels := by
      have ha : raw36079step2 = raw36079step1 := by apply Matrix.ext; unfold raw36079step2 raw36079step1; decide +kernel
      have hl : raw36079step1Labels = labelEmbedding1 ∘ raw36079step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36079step1 raw36079step1Labels raw36079step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2141 node2141Labels := by rfl

def raw36080 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36080Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36080step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw36080step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36080step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36080step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36080step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36080step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36080 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36080 raw36080Labels = mixedMoment B node2661 node2661Labels := by
  calc
    mixedMoment B raw36080 raw36080Labels = mixedMoment B raw36080step0 raw36080step0Labels := by
      have ha : raw36080step0 = (fun i j => raw36080 (permutation267 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36080step0 raw36080; decide +kernel
      have hl : raw36080step0Labels = raw36080Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36080 raw36080Labels permutation267 permutation7
    mixedMoment B raw36080step0 raw36080step0Labels = mixedMoment B raw36080step1 raw36080step1Labels := by
      have ha : raw36080step1 = -raw36080step0 := by apply Matrix.ext; change ∀ i j, raw36080step1 i j = -(raw36080step0 i j); unfold raw36080step1 raw36080step0; decide +kernel
      have hl : raw36080step1Labels = raw36080step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36080step1 raw36080step1Labels = mixedMoment B raw36080step2 raw36080step2Labels := by
      have ha : raw36080step2 = raw36080step1 := by apply Matrix.ext; unfold raw36080step2 raw36080step1; decide +kernel
      have hl : raw36080step1Labels = labelEmbedding1 ∘ raw36080step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36080step1 raw36080step1Labels raw36080step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2661 node2661Labels := by rfl

def raw36081 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![1, -1, 0], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2]]
def raw36081Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36081step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw36081step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36081step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw36081step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36081step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw36081step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36081step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw36081step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36081 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36081 raw36081Labels = mixedMoment B node2672 node2672Labels := by
  calc
    mixedMoment B raw36081 raw36081Labels = mixedMoment B raw36081step0 raw36081step0Labels := by
      have hz : ∀ j, raw36081 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw36081step0 = (fun i j => raw36081 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw36081step0 raw36081; decide +kernel
      have hl : raw36081step0Labels = raw36081Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36081 raw36081Labels permutation520 hz
    mixedMoment B raw36081step0 raw36081step0Labels = mixedMoment B raw36081step1 raw36081step1Labels := by
      have ha : raw36081step1 = (fun i j => raw36081step0 (permutation56 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36081step1 raw36081step0; decide +kernel
      have hl : raw36081step1Labels = raw36081step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36081step0 raw36081step0Labels permutation56 permutation7
    mixedMoment B raw36081step1 raw36081step1Labels = mixedMoment B raw36081step2 raw36081step2Labels := by
      have ha : raw36081step2 = -raw36081step1 := by apply Matrix.ext; change ∀ i j, raw36081step2 i j = -(raw36081step1 i j); unfold raw36081step2 raw36081step1; decide +kernel
      have hl : raw36081step2Labels = raw36081step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36081step2 raw36081step2Labels = mixedMoment B raw36081step3 raw36081step3Labels := by
      have ha : raw36081step3 = raw36081step2 := by apply Matrix.ext; unfold raw36081step3 raw36081step2; decide +kernel
      have hl : raw36081step2Labels = labelEmbedding1 ∘ raw36081step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36081step2 raw36081step2Labels raw36081step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2672 node2672Labels := by rfl

def raw36082 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw36082Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36082step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw36082step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36082step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36082step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36082step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36082step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36082 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36082 raw36082Labels = mixedMoment B node2662 node2662Labels := by
  calc
    mixedMoment B raw36082 raw36082Labels = mixedMoment B raw36082step0 raw36082step0Labels := by
      have ha : raw36082step0 = (fun i j => raw36082 (permutation267 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36082step0 raw36082; decide +kernel
      have hl : raw36082step0Labels = raw36082Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36082 raw36082Labels permutation267 permutation7
    mixedMoment B raw36082step0 raw36082step0Labels = mixedMoment B raw36082step1 raw36082step1Labels := by
      have ha : raw36082step1 = -raw36082step0 := by apply Matrix.ext; change ∀ i j, raw36082step1 i j = -(raw36082step0 i j); unfold raw36082step1 raw36082step0; decide +kernel
      have hl : raw36082step1Labels = raw36082step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36082step1 raw36082step1Labels = mixedMoment B raw36082step2 raw36082step2Labels := by
      have ha : raw36082step2 = raw36082step1 := by apply Matrix.ext; unfold raw36082step2 raw36082step1; decide +kernel
      have hl : raw36082step1Labels = labelEmbedding1 ∘ raw36082step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36082step1 raw36082step1Labels raw36082step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2662 node2662Labels := by rfl

def raw36083 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![0, 0, 0], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36083Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36083step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36083step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36083step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 3, -2], ![-1, 0, 1], ![-1, -1, 2]]
def raw36083step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36083step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw36083step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36083step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw36083step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36083 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36083 raw36083Labels = mixedMoment B node2272 node2272Labels := by
  calc
    mixedMoment B raw36083 raw36083Labels = mixedMoment B raw36083step0 raw36083step0Labels := by
      have hz : ∀ j, raw36083 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36083step0 = (fun i j => raw36083 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36083step0 raw36083; decide +kernel
      have hl : raw36083step0Labels = raw36083Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36083 raw36083Labels permutation346 hz
    mixedMoment B raw36083step0 raw36083step0Labels = mixedMoment B raw36083step1 raw36083step1Labels := by
      have ha : raw36083step1 = (fun i j => raw36083step0 (permutation51 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36083step1 raw36083step0; decide +kernel
      have hl : raw36083step1Labels = raw36083step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36083step0 raw36083step0Labels permutation51 permutation5
    mixedMoment B raw36083step1 raw36083step1Labels = mixedMoment B raw36083step2 raw36083step2Labels := by
      have ha : raw36083step2 = -raw36083step1 := by apply Matrix.ext; change ∀ i j, raw36083step2 i j = -(raw36083step1 i j); unfold raw36083step2 raw36083step1; decide +kernel
      have hl : raw36083step2Labels = raw36083step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36083step2 raw36083step2Labels = mixedMoment B raw36083step3 raw36083step3Labels := by
      have ha : raw36083step3 = raw36083step2 := by apply Matrix.ext; unfold raw36083step3 raw36083step2; decide +kernel
      have hl : raw36083step2Labels = labelEmbedding1 ∘ raw36083step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36083step2 raw36083step2Labels raw36083step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2272 node2272Labels := by rfl

def raw36084 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 0, 3], ![0, 0, 0], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36084Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36084step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 0, 3], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36084step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36084step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw36084step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36084step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw36084step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36084step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw36084step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36084 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36084 raw36084Labels = mixedMoment B node2152 node2152Labels := by
  calc
    mixedMoment B raw36084 raw36084Labels = mixedMoment B raw36084step0 raw36084step0Labels := by
      have hz : ∀ j, raw36084 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36084step0 = (fun i j => raw36084 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36084step0 raw36084; decide +kernel
      have hl : raw36084step0Labels = raw36084Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36084 raw36084Labels permutation346 hz
    mixedMoment B raw36084step0 raw36084step0Labels = mixedMoment B raw36084step1 raw36084step1Labels := by
      have ha : raw36084step1 = (fun i j => raw36084step0 (permutation58 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36084step1 raw36084step0; decide +kernel
      have hl : raw36084step1Labels = raw36084step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36084step0 raw36084step0Labels permutation58 permutation7
    mixedMoment B raw36084step1 raw36084step1Labels = mixedMoment B raw36084step2 raw36084step2Labels := by
      have ha : raw36084step2 = -raw36084step1 := by apply Matrix.ext; change ∀ i j, raw36084step2 i j = -(raw36084step1 i j); unfold raw36084step2 raw36084step1; decide +kernel
      have hl : raw36084step2Labels = raw36084step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36084step2 raw36084step2Labels = mixedMoment B raw36084step3 raw36084step3Labels := by
      have ha : raw36084step3 = raw36084step2 := by apply Matrix.ext; unfold raw36084step3 raw36084step2; decide +kernel
      have hl : raw36084step2Labels = labelEmbedding1 ∘ raw36084step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36084step2 raw36084step2Labels raw36084step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2152 node2152Labels := by rfl

def raw36085 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![-1, 1, 0], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36085Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36085step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw36085step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36085step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw36085step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36085step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw36085step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36085 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36085 raw36085Labels = mixedMoment B node2653 node2653Labels := by
  calc
    mixedMoment B raw36085 raw36085Labels = mixedMoment B raw36085step0 raw36085step0Labels := by
      have ha : raw36085step0 = (fun i j => raw36085 (permutation267 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36085step0 raw36085; decide +kernel
      have hl : raw36085step0Labels = raw36085Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36085 raw36085Labels permutation267 permutation7
    mixedMoment B raw36085step0 raw36085step0Labels = mixedMoment B raw36085step1 raw36085step1Labels := by
      have ha : raw36085step1 = -raw36085step0 := by apply Matrix.ext; change ∀ i j, raw36085step1 i j = -(raw36085step0 i j); unfold raw36085step1 raw36085step0; decide +kernel
      have hl : raw36085step1Labels = raw36085step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36085step1 raw36085step1Labels = mixedMoment B raw36085step2 raw36085step2Labels := by
      have ha : raw36085step2 = raw36085step1 := by apply Matrix.ext; unfold raw36085step2 raw36085step1; decide +kernel
      have hl : raw36085step1Labels = labelEmbedding1 ∘ raw36085step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36085step1 raw36085step1Labels raw36085step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2653 node2653Labels := by rfl

def raw36086 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![0, 0, 0], ![2, -1, -1], ![0, 0, 0], ![2, 0, -2]]
def raw36086Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36086step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![0, 0, 0], ![2, -1, -1], ![2, 0, -2]]
def raw36086step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36086step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![2, -1, -1], ![2, 0, -2]]
def raw36086step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36086step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![-1, -1, 2], ![-2, 0, 2]]
def raw36086step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36086step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw36086step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36086step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw36086step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36086 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36086 raw36086Labels = mixedMoment B node2686 node2686Labels := by
  calc
    mixedMoment B raw36086 raw36086Labels = mixedMoment B raw36086step0 raw36086step0Labels := by
      have hz : ∀ j, raw36086 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw36086step0 = (fun i j => raw36086 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw36086step0 raw36086; decide +kernel
      have hl : raw36086step0Labels = raw36086Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36086 raw36086Labels permutation520 hz
    mixedMoment B raw36086step0 raw36086step0Labels = mixedMoment B raw36086step1 raw36086step1Labels := by
      have hz : ∀ j, raw36086step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw36086step1 = (fun i j => raw36086step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw36086step1 raw36086step0; decide +kernel
      have hl : raw36086step1Labels = raw36086step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36086step0 raw36086step0Labels permutation80 hz
    mixedMoment B raw36086step1 raw36086step1Labels = mixedMoment B raw36086step2 raw36086step2Labels := by
      have ha : raw36086step2 = (fun i j => raw36086step1 (permutation14 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36086step2 raw36086step1; decide +kernel
      have hl : raw36086step2Labels = raw36086step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36086step1 raw36086step1Labels permutation14 permutation7
    mixedMoment B raw36086step2 raw36086step2Labels = mixedMoment B raw36086step3 raw36086step3Labels := by
      have ha : raw36086step3 = -raw36086step2 := by apply Matrix.ext; change ∀ i j, raw36086step3 i j = -(raw36086step2 i j); unfold raw36086step3 raw36086step2; decide +kernel
      have hl : raw36086step3Labels = raw36086step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36086step3 raw36086step3Labels = mixedMoment B raw36086step4 raw36086step4Labels := by
      have ha : raw36086step4 = raw36086step3 := by apply Matrix.ext; unfold raw36086step4 raw36086step3; decide +kernel
      have hl : raw36086step3Labels = labelEmbedding1 ∘ raw36086step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36086step3 raw36086step3Labels raw36086step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2686 node2686Labels := by rfl

def raw36087 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![0, 0, 0], ![2, -1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw36087Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36087step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![2, -1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw36087step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36087step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw36087step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36087step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw36087step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36087step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw36087step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36087 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36087 raw36087Labels = mixedMoment B node2673 node2673Labels := by
  calc
    mixedMoment B raw36087 raw36087Labels = mixedMoment B raw36087step0 raw36087step0Labels := by
      have hz : ∀ j, raw36087 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36087step0 = (fun i j => raw36087 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36087step0 raw36087; decide +kernel
      have hl : raw36087step0Labels = raw36087Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36087 raw36087Labels permutation346 hz
    mixedMoment B raw36087step0 raw36087step0Labels = mixedMoment B raw36087step1 raw36087step1Labels := by
      have ha : raw36087step1 = (fun i j => raw36087step0 (permutation58 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36087step1 raw36087step0; decide +kernel
      have hl : raw36087step1Labels = raw36087step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36087step0 raw36087step0Labels permutation58 permutation7
    mixedMoment B raw36087step1 raw36087step1Labels = mixedMoment B raw36087step2 raw36087step2Labels := by
      have ha : raw36087step2 = -raw36087step1 := by apply Matrix.ext; change ∀ i j, raw36087step2 i j = -(raw36087step1 i j); unfold raw36087step2 raw36087step1; decide +kernel
      have hl : raw36087step2Labels = raw36087step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36087step2 raw36087step2Labels = mixedMoment B raw36087step3 raw36087step3Labels := by
      have ha : raw36087step3 = raw36087step2 := by apply Matrix.ext; unfold raw36087step3 raw36087step2; decide +kernel
      have hl : raw36087step2Labels = labelEmbedding1 ∘ raw36087step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36087step2 raw36087step2Labels raw36087step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2673 node2673Labels := by rfl

def raw36088 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw36088Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36088step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw36088step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36088step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 3, -2], ![-2, 0, 2]]
def raw36088step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36088step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -3, 2], ![2, 0, -2]]
def raw36088step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36088step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -3, 2], ![2, 0, -2]]
def raw36088step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36088 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36088 raw36088Labels = mixedMoment B node2249 node2249Labels := by
  calc
    mixedMoment B raw36088 raw36088Labels = mixedMoment B raw36088step0 raw36088step0Labels := by
      have hz : ∀ j, raw36088 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36088step0 = (fun i j => raw36088 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36088step0 raw36088; decide +kernel
      have hl : raw36088step0Labels = raw36088Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36088 raw36088Labels permutation346 hz
    mixedMoment B raw36088step0 raw36088step0Labels = mixedMoment B raw36088step1 raw36088step1Labels := by
      have ha : raw36088step1 = (fun i j => raw36088step0 (permutation42 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36088step1 raw36088step0; decide +kernel
      have hl : raw36088step1Labels = raw36088step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36088step0 raw36088step0Labels permutation42 permutation5
    mixedMoment B raw36088step1 raw36088step1Labels = mixedMoment B raw36088step2 raw36088step2Labels := by
      have ha : raw36088step2 = -raw36088step1 := by apply Matrix.ext; change ∀ i j, raw36088step2 i j = -(raw36088step1 i j); unfold raw36088step2 raw36088step1; decide +kernel
      have hl : raw36088step2Labels = raw36088step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36088step2 raw36088step2Labels = mixedMoment B raw36088step3 raw36088step3Labels := by
      have ha : raw36088step3 = raw36088step2 := by apply Matrix.ext; unfold raw36088step3 raw36088step2; decide +kernel
      have hl : raw36088step2Labels = labelEmbedding1 ∘ raw36088step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36088step2 raw36088step2Labels raw36088step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2249 node2249Labels := by rfl

def raw36089 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 0, 3], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw36089Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36089step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 0, 3], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw36089step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36089step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -2, 2], ![-1, 0, 1], ![-2, 0, 2]]
def raw36089step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36089step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw36089step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36089step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw36089step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36089 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36089 raw36089Labels = mixedMoment B node2157 node2157Labels := by
  calc
    mixedMoment B raw36089 raw36089Labels = mixedMoment B raw36089step0 raw36089step0Labels := by
      have hz : ∀ j, raw36089 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36089step0 = (fun i j => raw36089 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36089step0 raw36089; decide +kernel
      have hl : raw36089step0Labels = raw36089Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36089 raw36089Labels permutation346 hz
    mixedMoment B raw36089step0 raw36089step0Labels = mixedMoment B raw36089step1 raw36089step1Labels := by
      have ha : raw36089step1 = (fun i j => raw36089step0 (permutation58 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36089step1 raw36089step0; decide +kernel
      have hl : raw36089step1Labels = raw36089step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36089step0 raw36089step0Labels permutation58 permutation7
    mixedMoment B raw36089step1 raw36089step1Labels = mixedMoment B raw36089step2 raw36089step2Labels := by
      have ha : raw36089step2 = -raw36089step1 := by apply Matrix.ext; change ∀ i j, raw36089step2 i j = -(raw36089step1 i j); unfold raw36089step2 raw36089step1; decide +kernel
      have hl : raw36089step2Labels = raw36089step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36089step2 raw36089step2Labels = mixedMoment B raw36089step3 raw36089step3Labels := by
      have ha : raw36089step3 = raw36089step2 := by apply Matrix.ext; unfold raw36089step3 raw36089step2; decide +kernel
      have hl : raw36089step2Labels = labelEmbedding1 ∘ raw36089step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36089step2 raw36089step2Labels raw36089step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2157 node2157Labels := by rfl

def raw36090 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw36090Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36090step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 0, 2]]
def raw36090step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36090step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw36090step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36090step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw36090step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36090 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36090 raw36090Labels = mixedMoment B node2654 node2654Labels := by
  calc
    mixedMoment B raw36090 raw36090Labels = mixedMoment B raw36090step0 raw36090step0Labels := by
      have ha : raw36090step0 = (fun i j => raw36090 (permutation267 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36090step0 raw36090; decide +kernel
      have hl : raw36090step0Labels = raw36090Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36090 raw36090Labels permutation267 permutation7
    mixedMoment B raw36090step0 raw36090step0Labels = mixedMoment B raw36090step1 raw36090step1Labels := by
      have ha : raw36090step1 = -raw36090step0 := by apply Matrix.ext; change ∀ i j, raw36090step1 i j = -(raw36090step0 i j); unfold raw36090step1 raw36090step0; decide +kernel
      have hl : raw36090step1Labels = raw36090step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36090step1 raw36090step1Labels = mixedMoment B raw36090step2 raw36090step2Labels := by
      have ha : raw36090step2 = raw36090step1 := by apply Matrix.ext; unfold raw36090step2 raw36090step1; decide +kernel
      have hl : raw36090step1Labels = labelEmbedding1 ∘ raw36090step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36090step1 raw36090step1Labels raw36090step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2654 node2654Labels := by rfl

def raw36091 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw36091Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36091step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw36091step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36091step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw36091step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36091step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw36091step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36091step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw36091step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36091 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36091 raw36091Labels = mixedMoment B node2677 node2677Labels := by
  calc
    mixedMoment B raw36091 raw36091Labels = mixedMoment B raw36091step0 raw36091step0Labels := by
      have hz : ∀ j, raw36091 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36091step0 = (fun i j => raw36091 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36091step0 raw36091; decide +kernel
      have hl : raw36091step0Labels = raw36091Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36091 raw36091Labels permutation346 hz
    mixedMoment B raw36091step0 raw36091step0Labels = mixedMoment B raw36091step1 raw36091step1Labels := by
      have ha : raw36091step1 = (fun i j => raw36091step0 (permutation58 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36091step1 raw36091step0; decide +kernel
      have hl : raw36091step1Labels = raw36091step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36091step0 raw36091step0Labels permutation58 permutation7
    mixedMoment B raw36091step1 raw36091step1Labels = mixedMoment B raw36091step2 raw36091step2Labels := by
      have ha : raw36091step2 = -raw36091step1 := by apply Matrix.ext; change ∀ i j, raw36091step2 i j = -(raw36091step1 i j); unfold raw36091step2 raw36091step1; decide +kernel
      have hl : raw36091step2Labels = raw36091step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36091step2 raw36091step2Labels = mixedMoment B raw36091step3 raw36091step3Labels := by
      have ha : raw36091step3 = raw36091step2 := by apply Matrix.ext; unfold raw36091step3 raw36091step2; decide +kernel
      have hl : raw36091step2Labels = labelEmbedding1 ∘ raw36091step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36091step2 raw36091step2Labels raw36091step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2677 node2677Labels := by rfl

def raw36092 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![1, 1, -2]]
def raw36092Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36092step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![1, 0, -1], ![2, -2, 0], ![1, 1, -2]]
def raw36092step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36092step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw36092step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36092step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw36092step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36092step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw36092step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36092 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36092 raw36092Labels = mixedMoment B node2678 node2678Labels := by
  calc
    mixedMoment B raw36092 raw36092Labels = mixedMoment B raw36092step0 raw36092step0Labels := by
      have hz : ∀ j, raw36092 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36092step0 = (fun i j => raw36092 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36092step0 raw36092; decide +kernel
      have hl : raw36092step0Labels = raw36092Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36092 raw36092Labels permutation346 hz
    mixedMoment B raw36092step0 raw36092step0Labels = mixedMoment B raw36092step1 raw36092step1Labels := by
      have ha : raw36092step1 = (fun i j => raw36092step0 (permutation58 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36092step1 raw36092step0; decide +kernel
      have hl : raw36092step1Labels = raw36092step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36092step0 raw36092step0Labels permutation58 permutation7
    mixedMoment B raw36092step1 raw36092step1Labels = mixedMoment B raw36092step2 raw36092step2Labels := by
      have ha : raw36092step2 = -raw36092step1 := by apply Matrix.ext; change ∀ i j, raw36092step2 i j = -(raw36092step1 i j); unfold raw36092step2 raw36092step1; decide +kernel
      have hl : raw36092step2Labels = raw36092step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36092step2 raw36092step2Labels = mixedMoment B raw36092step3 raw36092step3Labels := by
      have ha : raw36092step3 = raw36092step2 := by apply Matrix.ext; unfold raw36092step3 raw36092step2; decide +kernel
      have hl : raw36092step2Labels = labelEmbedding1 ∘ raw36092step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36092step2 raw36092step2Labels raw36092step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2678 node2678Labels := by rfl

def raw36093 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw36093Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36093step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw36093step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36093step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 3, -2], ![-1, 0, 1], ![-1, -2, 3]]
def raw36093step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36093step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 2, -3]]
def raw36093step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36093step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 2, -3]]
def raw36093step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36093 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36093 raw36093Labels = mixedMoment B node2256 node2256Labels := by
  calc
    mixedMoment B raw36093 raw36093Labels = mixedMoment B raw36093step0 raw36093step0Labels := by
      have hz : ∀ j, raw36093 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36093step0 = (fun i j => raw36093 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36093step0 raw36093; decide +kernel
      have hl : raw36093step0Labels = raw36093Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36093 raw36093Labels permutation346 hz
    mixedMoment B raw36093step0 raw36093step0Labels = mixedMoment B raw36093step1 raw36093step1Labels := by
      have ha : raw36093step1 = (fun i j => raw36093step0 (permutation38 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36093step1 raw36093step0; decide +kernel
      have hl : raw36093step1Labels = raw36093step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36093step0 raw36093step0Labels permutation38 permutation5
    mixedMoment B raw36093step1 raw36093step1Labels = mixedMoment B raw36093step2 raw36093step2Labels := by
      have ha : raw36093step2 = -raw36093step1 := by apply Matrix.ext; change ∀ i j, raw36093step2 i j = -(raw36093step1 i j); unfold raw36093step2 raw36093step1; decide +kernel
      have hl : raw36093step2Labels = raw36093step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36093step2 raw36093step2Labels = mixedMoment B raw36093step3 raw36093step3Labels := by
      have ha : raw36093step3 = raw36093step2 := by apply Matrix.ext; unfold raw36093step3 raw36093step2; decide +kernel
      have hl : raw36093step2Labels = labelEmbedding1 ∘ raw36093step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36093step2 raw36093step2Labels raw36093step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2256 node2256Labels := by rfl

def raw36094 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 0, 3], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw36094Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36094step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 0, 3], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw36094step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36094step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, -1, 3]]
def raw36094step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36094step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw36094step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36094step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw36094step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36094 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36094 raw36094Labels = mixedMoment B node2151 node2151Labels := by
  calc
    mixedMoment B raw36094 raw36094Labels = mixedMoment B raw36094step0 raw36094step0Labels := by
      have hz : ∀ j, raw36094 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36094step0 = (fun i j => raw36094 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36094step0 raw36094; decide +kernel
      have hl : raw36094step0Labels = raw36094Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36094 raw36094Labels permutation346 hz
    mixedMoment B raw36094step0 raw36094step0Labels = mixedMoment B raw36094step1 raw36094step1Labels := by
      have ha : raw36094step1 = (fun i j => raw36094step0 (permutation58 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36094step1 raw36094step0; decide +kernel
      have hl : raw36094step1Labels = raw36094step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36094step0 raw36094step0Labels permutation58 permutation7
    mixedMoment B raw36094step1 raw36094step1Labels = mixedMoment B raw36094step2 raw36094step2Labels := by
      have ha : raw36094step2 = -raw36094step1 := by apply Matrix.ext; change ∀ i j, raw36094step2 i j = -(raw36094step1 i j); unfold raw36094step2 raw36094step1; decide +kernel
      have hl : raw36094step2Labels = raw36094step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36094step2 raw36094step2Labels = mixedMoment B raw36094step3 raw36094step3Labels := by
      have ha : raw36094step3 = raw36094step2 := by apply Matrix.ext; unfold raw36094step3 raw36094step2; decide +kernel
      have hl : raw36094step2Labels = labelEmbedding1 ∘ raw36094step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36094step2 raw36094step2Labels raw36094step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2151 node2151Labels := by rfl

def raw36095 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw36095Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36095step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, -1, 3]]
def raw36095step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36095step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw36095step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36095step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw36095step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36095 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36095 raw36095Labels = mixedMoment B node2652 node2652Labels := by
  calc
    mixedMoment B raw36095 raw36095Labels = mixedMoment B raw36095step0 raw36095step0Labels := by
      have ha : raw36095step0 = (fun i j => raw36095 (permutation267 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36095step0 raw36095; decide +kernel
      have hl : raw36095step0Labels = raw36095Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36095 raw36095Labels permutation267 permutation7
    mixedMoment B raw36095step0 raw36095step0Labels = mixedMoment B raw36095step1 raw36095step1Labels := by
      have ha : raw36095step1 = -raw36095step0 := by apply Matrix.ext; change ∀ i j, raw36095step1 i j = -(raw36095step0 i j); unfold raw36095step1 raw36095step0; decide +kernel
      have hl : raw36095step1Labels = raw36095step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36095step1 raw36095step1Labels = mixedMoment B raw36095step2 raw36095step2Labels := by
      have ha : raw36095step2 = raw36095step1 := by apply Matrix.ext; unfold raw36095step2 raw36095step1; decide +kernel
      have hl : raw36095step1Labels = labelEmbedding1 ∘ raw36095step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36095step1 raw36095step1Labels raw36095step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2652 node2652Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
