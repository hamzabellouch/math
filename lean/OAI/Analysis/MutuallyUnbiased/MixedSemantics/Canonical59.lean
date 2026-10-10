import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes52
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw7552 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7552Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7552step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7552step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7552step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw7552step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7552step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw7552step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7552 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7552 raw7552Labels = mixedMoment B node3533 node3533Labels := by
  calc
    mixedMoment B raw7552 raw7552Labels = mixedMoment B raw7552step0 raw7552step0Labels := by
      have hz : ∀ j, raw7552 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7552step0 = (fun i j => raw7552 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7552step0 raw7552; decide +kernel
      have hl : raw7552step0Labels = raw7552Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7552 raw7552Labels permutation434 hz
    mixedMoment B raw7552step0 raw7552step0Labels = mixedMoment B raw7552step1 raw7552step1Labels := by
      have ha : raw7552step1 = (fun i j => raw7552step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7552step1 raw7552step0; decide +kernel
      have hl : raw7552step1Labels = raw7552step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7552step0 raw7552step0Labels permutation40 permutation2
    mixedMoment B raw7552step1 raw7552step1Labels = mixedMoment B raw7552step2 raw7552step2Labels := by
      have ha : raw7552step2 = -raw7552step1 := by apply Matrix.ext; change ∀ i j, raw7552step2 i j = -(raw7552step1 i j); unfold raw7552step2 raw7552step1; decide +kernel
      have hl : raw7552step2Labels = raw7552step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3533 node3533Labels := by rfl

def raw7553 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw7553Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7553step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw7553step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7553 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7553 raw7553Labels = mixedMoment B node2552 node2552Labels := by
  calc
    mixedMoment B raw7553 raw7553Labels = mixedMoment B raw7553step0 raw7553step0Labels := by
      have ha : raw7553step0 = (fun i j => raw7553 (permutation620 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7553step0 raw7553; decide +kernel
      have hl : raw7553step0Labels = raw7553Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7553 raw7553Labels permutation620 permutation2
    _ = mixedMoment B node2552 node2552Labels := by rfl

def raw7554 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7554Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7554step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw7554step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7554step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw7554step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7554 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7554 raw7554Labels = mixedMoment B node2034 node2034Labels := by
  calc
    mixedMoment B raw7554 raw7554Labels = mixedMoment B raw7554step0 raw7554step0Labels := by
      have ha : raw7554step0 = (fun i j => raw7554 (permutation173 i) (permutation4 j)) := by apply Matrix.ext; unfold raw7554step0 raw7554; decide +kernel
      have hl : raw7554step0Labels = raw7554Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7554 raw7554Labels permutation173 permutation4
    mixedMoment B raw7554step0 raw7554step0Labels = mixedMoment B raw7554step1 raw7554step1Labels := by
      have ha : raw7554step1 = -raw7554step0 := by apply Matrix.ext; change ∀ i j, raw7554step1 i j = -(raw7554step0 i j); unfold raw7554step1 raw7554step0; decide +kernel
      have hl : raw7554step1Labels = raw7554step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2034 node2034Labels := by rfl

def raw7555 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7555Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7555step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7555step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7555step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7555step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7555step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1]]
def raw7555step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7555step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw7555step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7555 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7555 raw7555Labels = mixedMoment B node3632 node3632Labels := by
  calc
    mixedMoment B raw7555 raw7555Labels = mixedMoment B raw7555step0 raw7555step0Labels := by
      have hz : ∀ j, raw7555 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7555step0 = (fun i j => raw7555 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7555step0 raw7555; decide +kernel
      have hl : raw7555step0Labels = raw7555Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7555 raw7555Labels permutation434 hz
    mixedMoment B raw7555step0 raw7555step0Labels = mixedMoment B raw7555step1 raw7555step1Labels := by
      have hz : ∀ j, raw7555step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7555step1 = (fun i j => raw7555step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7555step1 raw7555step0; decide +kernel
      have hl : raw7555step1Labels = raw7555step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7555step0 raw7555step0Labels permutation56 hz
    mixedMoment B raw7555step1 raw7555step1Labels = mixedMoment B raw7555step2 raw7555step2Labels := by
      have ha : raw7555step2 = (fun i j => raw7555step1 (permutation12 i) (permutation4 j)) := by apply Matrix.ext; unfold raw7555step2 raw7555step1; decide +kernel
      have hl : raw7555step2Labels = raw7555step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7555step1 raw7555step1Labels permutation12 permutation4
    mixedMoment B raw7555step2 raw7555step2Labels = mixedMoment B raw7555step3 raw7555step3Labels := by
      have ha : raw7555step3 = -raw7555step2 := by apply Matrix.ext; change ∀ i j, raw7555step3 i j = -(raw7555step2 i j); unfold raw7555step3 raw7555step2; decide +kernel
      have hl : raw7555step3Labels = raw7555step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3632 node3632Labels := by rfl

def raw7556 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw7556Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7556step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw7556step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7556step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw7556step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7556 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7556 raw7556Labels = mixedMoment B node2738 node2738Labels := by
  calc
    mixedMoment B raw7556 raw7556Labels = mixedMoment B raw7556step0 raw7556step0Labels := by
      have hz : ∀ j, raw7556 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw7556step0 = (fun i j => raw7556 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw7556step0 raw7556; decide +kernel
      have hl : raw7556step0Labels = raw7556Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7556 raw7556Labels permutation265 hz
    mixedMoment B raw7556step0 raw7556step0Labels = mixedMoment B raw7556step1 raw7556step1Labels := by
      have ha : raw7556step1 = (fun i j => raw7556step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7556step1 raw7556step0; decide +kernel
      have hl : raw7556step1Labels = raw7556step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7556step0 raw7556step0Labels permutation149 permutation2
    _ = mixedMoment B node2738 node2738Labels := by rfl

def raw7557 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![2, -2, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7557Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7557step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw7557step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7557step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw7557step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7557 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7557 raw7557Labels = mixedMoment B node3382 node3382Labels := by
  calc
    mixedMoment B raw7557 raw7557Labels = mixedMoment B raw7557step0 raw7557step0Labels := by
      have ha : raw7557step0 = (fun i j => raw7557 (permutation173 i) (permutation4 j)) := by apply Matrix.ext; unfold raw7557step0 raw7557; decide +kernel
      have hl : raw7557step0Labels = raw7557Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7557 raw7557Labels permutation173 permutation4
    mixedMoment B raw7557step0 raw7557step0Labels = mixedMoment B raw7557step1 raw7557step1Labels := by
      have ha : raw7557step1 = -raw7557step0 := by apply Matrix.ext; change ∀ i j, raw7557step1 i j = -(raw7557step0 i j); unfold raw7557step1 raw7557step0; decide +kernel
      have hl : raw7557step1Labels = raw7557step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3382 node3382Labels := by rfl

def raw7558 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw7558Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7558step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw7558step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7558step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw7558step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7558step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw7558step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7558step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw7558step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7558 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7558 raw7558Labels = mixedMoment B node4619 node4619Labels := by
  calc
    mixedMoment B raw7558 raw7558Labels = mixedMoment B raw7558step0 raw7558step0Labels := by
      have hz : ∀ j, raw7558 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7558step0 = (fun i j => raw7558 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7558step0 raw7558; decide +kernel
      have hl : raw7558step0Labels = raw7558Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7558 raw7558Labels permutation434 hz
    mixedMoment B raw7558step0 raw7558step0Labels = mixedMoment B raw7558step1 raw7558step1Labels := by
      have hz : ∀ j, raw7558step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7558step1 = (fun i j => raw7558step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7558step1 raw7558step0; decide +kernel
      have hl : raw7558step1Labels = raw7558step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7558step0 raw7558step0Labels permutation80 hz
    mixedMoment B raw7558step1 raw7558step1Labels = mixedMoment B raw7558step2 raw7558step2Labels := by
      have ha : raw7558step2 = (fun i j => raw7558step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7558step2 raw7558step1; decide +kernel
      have hl : raw7558step2Labels = raw7558step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7558step1 raw7558step1Labels permutation10 permutation3
    mixedMoment B raw7558step2 raw7558step2Labels = mixedMoment B raw7558step3 raw7558step3Labels := by
      have ha : raw7558step3 = raw7558step2 := by apply Matrix.ext; unfold raw7558step3 raw7558step2; decide +kernel
      have hl : raw7558step2Labels = labelEmbedding6 ∘ raw7558step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7558step2 raw7558step2Labels raw7558step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4619 node4619Labels := by rfl

def raw7559 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw7559Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7559step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw7559step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7559step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw7559step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7559 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7559 raw7559Labels = mixedMoment B node5170 node5170Labels := by
  calc
    mixedMoment B raw7559 raw7559Labels = mixedMoment B raw7559step0 raw7559step0Labels := by
      have hz : ∀ j, raw7559 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7559step0 = (fun i j => raw7559 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7559step0 raw7559; decide +kernel
      have hl : raw7559step0Labels = raw7559Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7559 raw7559Labels permutation434 hz
    mixedMoment B raw7559step0 raw7559step0Labels = mixedMoment B raw7559step1 raw7559step1Labels := by
      have ha : raw7559step1 = (fun i j => raw7559step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7559step1 raw7559step0; decide +kernel
      have hl : raw7559step1Labels = raw7559step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7559step0 raw7559step0Labels permutation38 permutation2
    _ = mixedMoment B node5170 node5170Labels := by rfl

def raw7560 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw7560Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7560step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw7560step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7560step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw7560step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7560 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7560 raw7560Labels = mixedMoment B node5170 node5170Labels := by
  calc
    mixedMoment B raw7560 raw7560Labels = mixedMoment B raw7560step0 raw7560step0Labels := by
      have hz : ∀ j, raw7560 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7560step0 = (fun i j => raw7560 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7560step0 raw7560; decide +kernel
      have hl : raw7560step0Labels = raw7560Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7560 raw7560Labels permutation346 hz
    mixedMoment B raw7560step0 raw7560step0Labels = mixedMoment B raw7560step1 raw7560step1Labels := by
      have ha : raw7560step1 = (fun i j => raw7560step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7560step1 raw7560step0; decide +kernel
      have hl : raw7560step1Labels = raw7560step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7560step0 raw7560step0Labels permutation38 permutation2
    _ = mixedMoment B node5170 node5170Labels := by rfl

def raw7561 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0]]
def raw7561Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7561step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0]]
def raw7561step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7561step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0]]
def raw7561step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7561step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw7561step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7561 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7561 raw7561Labels = mixedMoment B node5306 node5306Labels := by
  calc
    mixedMoment B raw7561 raw7561Labels = mixedMoment B raw7561step0 raw7561step0Labels := by
      have hz : ∀ j, raw7561 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7561step0 = (fun i j => raw7561 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7561step0 raw7561; decide +kernel
      have hl : raw7561step0Labels = raw7561Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7561 raw7561Labels permutation434 hz
    mixedMoment B raw7561step0 raw7561step0Labels = mixedMoment B raw7561step1 raw7561step1Labels := by
      have hz : ∀ j, raw7561step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7561step1 = (fun i j => raw7561step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7561step1 raw7561step0; decide +kernel
      have hl : raw7561step1Labels = raw7561step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7561step0 raw7561step0Labels permutation80 hz
    mixedMoment B raw7561step1 raw7561step1Labels = mixedMoment B raw7561step2 raw7561step2Labels := by
      have ha : raw7561step2 = (fun i j => raw7561step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7561step2 raw7561step1; decide +kernel
      have hl : raw7561step2Labels = raw7561step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7561step1 raw7561step1Labels permutation9 permutation2
    _ = mixedMoment B node5306 node5306Labels := by rfl

def raw7562 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw7562Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7562step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw7562step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7562step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw7562step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7562step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw7562step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7562step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw7562step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7562 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7562 raw7562Labels = mixedMoment B node4619 node4619Labels := by
  calc
    mixedMoment B raw7562 raw7562Labels = mixedMoment B raw7562step0 raw7562step0Labels := by
      have hz : ∀ j, raw7562 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7562step0 = (fun i j => raw7562 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7562step0 raw7562; decide +kernel
      have hl : raw7562step0Labels = raw7562Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7562 raw7562Labels permutation434 hz
    mixedMoment B raw7562step0 raw7562step0Labels = mixedMoment B raw7562step1 raw7562step1Labels := by
      have hz : ∀ j, raw7562step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7562step1 = (fun i j => raw7562step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7562step1 raw7562step0; decide +kernel
      have hl : raw7562step1Labels = raw7562step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7562step0 raw7562step0Labels permutation56 hz
    mixedMoment B raw7562step1 raw7562step1Labels = mixedMoment B raw7562step2 raw7562step2Labels := by
      have ha : raw7562step2 = (fun i j => raw7562step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7562step2 raw7562step1; decide +kernel
      have hl : raw7562step2Labels = raw7562step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7562step1 raw7562step1Labels permutation10 permutation3
    mixedMoment B raw7562step2 raw7562step2Labels = mixedMoment B raw7562step3 raw7562step3Labels := by
      have ha : raw7562step3 = raw7562step2 := by apply Matrix.ext; unfold raw7562step3 raw7562step2; decide +kernel
      have hl : raw7562step2Labels = labelEmbedding6 ∘ raw7562step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7562step2 raw7562step2Labels raw7562step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4619 node4619Labels := by rfl

def raw7563 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw7563Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7563step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw7563step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7563 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7563 raw7563Labels = mixedMoment B node5170 node5170Labels := by
  calc
    mixedMoment B raw7563 raw7563Labels = mixedMoment B raw7563step0 raw7563step0Labels := by
      have hz : ∀ j, raw7563 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7563step0 = (fun i j => raw7563 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7563step0 raw7563; decide +kernel
      have hl : raw7563step0Labels = raw7563Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7563 raw7563Labels permutation434 hz
    _ = mixedMoment B node5170 node5170Labels := by rfl

def raw7564 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw7564Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7564step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw7564step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7564step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw7564step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7564 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7564 raw7564Labels = mixedMoment B node5170 node5170Labels := by
  calc
    mixedMoment B raw7564 raw7564Labels = mixedMoment B raw7564step0 raw7564step0Labels := by
      have hz : ∀ j, raw7564 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw7564step0 = (fun i j => raw7564 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw7564step0 raw7564; decide +kernel
      have hl : raw7564step0Labels = raw7564Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7564 raw7564Labels permutation265 hz
    mixedMoment B raw7564step0 raw7564step0Labels = mixedMoment B raw7564step1 raw7564step1Labels := by
      have ha : raw7564step1 = (fun i j => raw7564step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7564step1 raw7564step0; decide +kernel
      have hl : raw7564step1Labels = raw7564step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7564step0 raw7564step0Labels permutation38 permutation2
    _ = mixedMoment B node5170 node5170Labels := by rfl

def raw7565 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0]]
def raw7565Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7565step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0]]
def raw7565step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7565step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0]]
def raw7565step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7565step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw7565step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7565 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7565 raw7565Labels = mixedMoment B node5306 node5306Labels := by
  calc
    mixedMoment B raw7565 raw7565Labels = mixedMoment B raw7565step0 raw7565step0Labels := by
      have hz : ∀ j, raw7565 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7565step0 = (fun i j => raw7565 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7565step0 raw7565; decide +kernel
      have hl : raw7565step0Labels = raw7565Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7565 raw7565Labels permutation434 hz
    mixedMoment B raw7565step0 raw7565step0Labels = mixedMoment B raw7565step1 raw7565step1Labels := by
      have hz : ∀ j, raw7565step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7565step1 = (fun i j => raw7565step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7565step1 raw7565step0; decide +kernel
      have hl : raw7565step1Labels = raw7565step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7565step0 raw7565step0Labels permutation56 hz
    mixedMoment B raw7565step1 raw7565step1Labels = mixedMoment B raw7565step2 raw7565step2Labels := by
      have ha : raw7565step2 = (fun i j => raw7565step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7565step2 raw7565step1; decide +kernel
      have hl : raw7565step2Labels = raw7565step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7565step1 raw7565step1Labels permutation9 permutation2
    _ = mixedMoment B node5306 node5306Labels := by rfl

def raw7566 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw7566Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7566step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw7566step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7566step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw7566step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7566step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw7566step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7566step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw7566step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7566 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7566 raw7566Labels = mixedMoment B node4619 node4619Labels := by
  calc
    mixedMoment B raw7566 raw7566Labels = mixedMoment B raw7566step0 raw7566step0Labels := by
      have hz : ∀ j, raw7566 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7566step0 = (fun i j => raw7566 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7566step0 raw7566; decide +kernel
      have hl : raw7566step0Labels = raw7566Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7566 raw7566Labels permutation346 hz
    mixedMoment B raw7566step0 raw7566step0Labels = mixedMoment B raw7566step1 raw7566step1Labels := by
      have hz : ∀ j, raw7566step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7566step1 = (fun i j => raw7566step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7566step1 raw7566step0; decide +kernel
      have hl : raw7566step1Labels = raw7566step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7566step0 raw7566step0Labels permutation56 hz
    mixedMoment B raw7566step1 raw7566step1Labels = mixedMoment B raw7566step2 raw7566step2Labels := by
      have ha : raw7566step2 = (fun i j => raw7566step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7566step2 raw7566step1; decide +kernel
      have hl : raw7566step2Labels = raw7566step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7566step1 raw7566step1Labels permutation10 permutation3
    mixedMoment B raw7566step2 raw7566step2Labels = mixedMoment B raw7566step3 raw7566step3Labels := by
      have ha : raw7566step3 = raw7566step2 := by apply Matrix.ext; unfold raw7566step3 raw7566step2; decide +kernel
      have hl : raw7566step2Labels = labelEmbedding6 ∘ raw7566step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7566step2 raw7566step2Labels raw7566step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4619 node4619Labels := by rfl

def raw7567 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw7567Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7567step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw7567step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7567 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7567 raw7567Labels = mixedMoment B node5170 node5170Labels := by
  calc
    mixedMoment B raw7567 raw7567Labels = mixedMoment B raw7567step0 raw7567step0Labels := by
      have hz : ∀ j, raw7567 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7567step0 = (fun i j => raw7567 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7567step0 raw7567; decide +kernel
      have hl : raw7567step0Labels = raw7567Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7567 raw7567Labels permutation346 hz
    _ = mixedMoment B node5170 node5170Labels := by rfl

def raw7568 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw7568Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7568step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw7568step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7568 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7568 raw7568Labels = mixedMoment B node5170 node5170Labels := by
  calc
    mixedMoment B raw7568 raw7568Labels = mixedMoment B raw7568step0 raw7568step0Labels := by
      have hz : ∀ j, raw7568 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw7568step0 = (fun i j => raw7568 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw7568step0 raw7568; decide +kernel
      have hl : raw7568step0Labels = raw7568Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7568 raw7568Labels permutation265 hz
    _ = mixedMoment B node5170 node5170Labels := by rfl

def raw7569 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0]]
def raw7569Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7569step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0]]
def raw7569step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7569step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0]]
def raw7569step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7569step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw7569step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7569 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7569 raw7569Labels = mixedMoment B node5306 node5306Labels := by
  calc
    mixedMoment B raw7569 raw7569Labels = mixedMoment B raw7569step0 raw7569step0Labels := by
      have hz : ∀ j, raw7569 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7569step0 = (fun i j => raw7569 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7569step0 raw7569; decide +kernel
      have hl : raw7569step0Labels = raw7569Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7569 raw7569Labels permutation346 hz
    mixedMoment B raw7569step0 raw7569step0Labels = mixedMoment B raw7569step1 raw7569step1Labels := by
      have hz : ∀ j, raw7569step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7569step1 = (fun i j => raw7569step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7569step1 raw7569step0; decide +kernel
      have hl : raw7569step1Labels = raw7569step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7569step0 raw7569step0Labels permutation56 hz
    mixedMoment B raw7569step1 raw7569step1Labels = mixedMoment B raw7569step2 raw7569step2Labels := by
      have ha : raw7569step2 = (fun i j => raw7569step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7569step2 raw7569step1; decide +kernel
      have hl : raw7569step2Labels = raw7569step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7569step1 raw7569step1Labels permutation9 permutation2
    _ = mixedMoment B node5306 node5306Labels := by rfl

def raw7570 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw7570Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7570step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw7570step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7570step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw7570step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7570step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![2, 0, -2], ![2, -2, 0]]
def raw7570step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7570step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -2, 0], ![2, 0, -2]]
def raw7570step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7570 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7570 raw7570Labels = mixedMoment B node4627 node4627Labels := by
  calc
    mixedMoment B raw7570 raw7570Labels = mixedMoment B raw7570step0 raw7570step0Labels := by
      have hz : ∀ j, raw7570 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7570step0 = (fun i j => raw7570 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7570step0 raw7570; decide +kernel
      have hl : raw7570step0Labels = raw7570Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7570 raw7570Labels permutation434 hz
    mixedMoment B raw7570step0 raw7570step0Labels = mixedMoment B raw7570step1 raw7570step1Labels := by
      have hz : ∀ j, raw7570step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7570step1 = (fun i j => raw7570step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7570step1 raw7570step0; decide +kernel
      have hl : raw7570step1Labels = raw7570step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7570step0 raw7570step0Labels permutation80 hz
    mixedMoment B raw7570step1 raw7570step1Labels = mixedMoment B raw7570step2 raw7570step2Labels := by
      have hz : ∀ j, raw7570step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw7570step2 = (fun i j => raw7570step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw7570step2 raw7570step1; decide +kernel
      have hl : raw7570step2Labels = raw7570step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7570step1 raw7570step1Labels permutation14 hz
    mixedMoment B raw7570step2 raw7570step2Labels = mixedMoment B raw7570step3 raw7570step3Labels := by
      have ha : raw7570step3 = (fun i j => raw7570step2 (permutation3 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7570step3 raw7570step2; decide +kernel
      have hl : raw7570step3Labels = raw7570step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7570step2 raw7570step2Labels permutation3 permutation2
    _ = mixedMoment B node4627 node4627Labels := by rfl

def raw7571 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw7571Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7571step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw7571step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7571step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw7571step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7571step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw7571step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7571 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7571 raw7571Labels = mixedMoment B node5176 node5176Labels := by
  calc
    mixedMoment B raw7571 raw7571Labels = mixedMoment B raw7571step0 raw7571step0Labels := by
      have hz : ∀ j, raw7571 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7571step0 = (fun i j => raw7571 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7571step0 raw7571; decide +kernel
      have hl : raw7571step0Labels = raw7571Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7571 raw7571Labels permutation434 hz
    mixedMoment B raw7571step0 raw7571step0Labels = mixedMoment B raw7571step1 raw7571step1Labels := by
      have hz : ∀ j, raw7571step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7571step1 = (fun i j => raw7571step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7571step1 raw7571step0; decide +kernel
      have hl : raw7571step1Labels = raw7571step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7571step0 raw7571step0Labels permutation80 hz
    mixedMoment B raw7571step1 raw7571step1Labels = mixedMoment B raw7571step2 raw7571step2Labels := by
      have ha : raw7571step2 = (fun i j => raw7571step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7571step2 raw7571step1; decide +kernel
      have hl : raw7571step2Labels = raw7571step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7571step1 raw7571step1Labels permutation9 permutation2
    _ = mixedMoment B node5176 node5176Labels := by rfl

def raw7572 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw7572Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7572step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw7572step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7572step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw7572step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7572step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw7572step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7572 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7572 raw7572Labels = mixedMoment B node5176 node5176Labels := by
  calc
    mixedMoment B raw7572 raw7572Labels = mixedMoment B raw7572step0 raw7572step0Labels := by
      have hz : ∀ j, raw7572 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7572step0 = (fun i j => raw7572 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7572step0 raw7572; decide +kernel
      have hl : raw7572step0Labels = raw7572Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7572 raw7572Labels permutation434 hz
    mixedMoment B raw7572step0 raw7572step0Labels = mixedMoment B raw7572step1 raw7572step1Labels := by
      have hz : ∀ j, raw7572step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7572step1 = (fun i j => raw7572step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7572step1 raw7572step0; decide +kernel
      have hl : raw7572step1Labels = raw7572step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7572step0 raw7572step0Labels permutation56 hz
    mixedMoment B raw7572step1 raw7572step1Labels = mixedMoment B raw7572step2 raw7572step2Labels := by
      have ha : raw7572step2 = (fun i j => raw7572step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7572step2 raw7572step1; decide +kernel
      have hl : raw7572step2Labels = raw7572step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7572step1 raw7572step1Labels permutation9 permutation2
    _ = mixedMoment B node5176 node5176Labels := by rfl

def raw7573 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw7573Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7573step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw7573step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7573step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw7573step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7573step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw7573step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7573 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7573 raw7573Labels = mixedMoment B node5176 node5176Labels := by
  calc
    mixedMoment B raw7573 raw7573Labels = mixedMoment B raw7573step0 raw7573step0Labels := by
      have hz : ∀ j, raw7573 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7573step0 = (fun i j => raw7573 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7573step0 raw7573; decide +kernel
      have hl : raw7573step0Labels = raw7573Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7573 raw7573Labels permutation346 hz
    mixedMoment B raw7573step0 raw7573step0Labels = mixedMoment B raw7573step1 raw7573step1Labels := by
      have hz : ∀ j, raw7573step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7573step1 = (fun i j => raw7573step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7573step1 raw7573step0; decide +kernel
      have hl : raw7573step1Labels = raw7573step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7573step0 raw7573step0Labels permutation56 hz
    mixedMoment B raw7573step1 raw7573step1Labels = mixedMoment B raw7573step2 raw7573step2Labels := by
      have ha : raw7573step2 = (fun i j => raw7573step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7573step2 raw7573step1; decide +kernel
      have hl : raw7573step2Labels = raw7573step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7573step1 raw7573step1Labels permutation9 permutation2
    _ = mixedMoment B node5176 node5176Labels := by rfl

def raw7574 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw7574Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7574step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw7574step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7574step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw7574step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7574step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![2, 0, -2], ![1, -1, 0]]
def raw7574step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7574step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![2, 0, -2]]
def raw7574step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7574 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7574 raw7574Labels = mixedMoment B node5308 node5308Labels := by
  calc
    mixedMoment B raw7574 raw7574Labels = mixedMoment B raw7574step0 raw7574step0Labels := by
      have hz : ∀ j, raw7574 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7574step0 = (fun i j => raw7574 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7574step0 raw7574; decide +kernel
      have hl : raw7574step0Labels = raw7574Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7574 raw7574Labels permutation434 hz
    mixedMoment B raw7574step0 raw7574step0Labels = mixedMoment B raw7574step1 raw7574step1Labels := by
      have hz : ∀ j, raw7574step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7574step1 = (fun i j => raw7574step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7574step1 raw7574step0; decide +kernel
      have hl : raw7574step1Labels = raw7574step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7574step0 raw7574step0Labels permutation80 hz
    mixedMoment B raw7574step1 raw7574step1Labels = mixedMoment B raw7574step2 raw7574step2Labels := by
      have hz : ∀ j, raw7574step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw7574step2 = (fun i j => raw7574step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw7574step2 raw7574step1; decide +kernel
      have hl : raw7574step2Labels = raw7574step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7574step1 raw7574step1Labels permutation14 hz
    mixedMoment B raw7574step2 raw7574step2Labels = mixedMoment B raw7574step3 raw7574step3Labels := by
      have ha : raw7574step3 = (fun i j => raw7574step2 (permutation3 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7574step3 raw7574step2; decide +kernel
      have hl : raw7574step3Labels = raw7574step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7574step2 raw7574step2Labels permutation3 permutation2
    _ = mixedMoment B node5308 node5308Labels := by rfl

def raw7575 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw7575Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7575step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw7575step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7575step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw7575step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7575step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw7575step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7575step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7575step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7575 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7575 raw7575Labels = mixedMoment B node3889 node3889Labels := by
  calc
    mixedMoment B raw7575 raw7575Labels = mixedMoment B raw7575step0 raw7575step0Labels := by
      have hz : ∀ j, raw7575 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7575step0 = (fun i j => raw7575 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7575step0 raw7575; decide +kernel
      have hl : raw7575step0Labels = raw7575Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7575 raw7575Labels permutation434 hz
    mixedMoment B raw7575step0 raw7575step0Labels = mixedMoment B raw7575step1 raw7575step1Labels := by
      have hz : ∀ j, raw7575step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7575step1 = (fun i j => raw7575step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7575step1 raw7575step0; decide +kernel
      have hl : raw7575step1Labels = raw7575step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7575step0 raw7575step0Labels permutation80 hz
    mixedMoment B raw7575step1 raw7575step1Labels = mixedMoment B raw7575step2 raw7575step2Labels := by
      have ha : raw7575step2 = (fun i j => raw7575step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7575step2 raw7575step1; decide +kernel
      have hl : raw7575step2Labels = raw7575step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7575step1 raw7575step1Labels permutation31 permutation3
    mixedMoment B raw7575step2 raw7575step2Labels = mixedMoment B raw7575step3 raw7575step3Labels := by
      have ha : raw7575step3 = -raw7575step2 := by apply Matrix.ext; change ∀ i j, raw7575step3 i j = -(raw7575step2 i j); unfold raw7575step3 raw7575step2; decide +kernel
      have hl : raw7575step3Labels = raw7575step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3889 node3889Labels := by rfl

def raw7576 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw7576Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7576step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw7576step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7576step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw7576step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7576step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw7576step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7576step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7576step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7576 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7576 raw7576Labels = mixedMoment B node3889 node3889Labels := by
  calc
    mixedMoment B raw7576 raw7576Labels = mixedMoment B raw7576step0 raw7576step0Labels := by
      have hz : ∀ j, raw7576 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7576step0 = (fun i j => raw7576 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7576step0 raw7576; decide +kernel
      have hl : raw7576step0Labels = raw7576Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7576 raw7576Labels permutation434 hz
    mixedMoment B raw7576step0 raw7576step0Labels = mixedMoment B raw7576step1 raw7576step1Labels := by
      have hz : ∀ j, raw7576step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7576step1 = (fun i j => raw7576step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7576step1 raw7576step0; decide +kernel
      have hl : raw7576step1Labels = raw7576step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7576step0 raw7576step0Labels permutation56 hz
    mixedMoment B raw7576step1 raw7576step1Labels = mixedMoment B raw7576step2 raw7576step2Labels := by
      have ha : raw7576step2 = (fun i j => raw7576step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7576step2 raw7576step1; decide +kernel
      have hl : raw7576step2Labels = raw7576step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7576step1 raw7576step1Labels permutation31 permutation3
    mixedMoment B raw7576step2 raw7576step2Labels = mixedMoment B raw7576step3 raw7576step3Labels := by
      have ha : raw7576step3 = -raw7576step2 := by apply Matrix.ext; change ∀ i j, raw7576step3 i j = -(raw7576step2 i j); unfold raw7576step3 raw7576step2; decide +kernel
      have hl : raw7576step3Labels = raw7576step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3889 node3889Labels := by rfl

def raw7577 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw7577Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7577step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw7577step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7577step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw7577step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7577step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw7577step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7577step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7577step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7577 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7577 raw7577Labels = mixedMoment B node3889 node3889Labels := by
  calc
    mixedMoment B raw7577 raw7577Labels = mixedMoment B raw7577step0 raw7577step0Labels := by
      have hz : ∀ j, raw7577 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7577step0 = (fun i j => raw7577 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7577step0 raw7577; decide +kernel
      have hl : raw7577step0Labels = raw7577Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7577 raw7577Labels permutation346 hz
    mixedMoment B raw7577step0 raw7577step0Labels = mixedMoment B raw7577step1 raw7577step1Labels := by
      have hz : ∀ j, raw7577step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7577step1 = (fun i j => raw7577step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7577step1 raw7577step0; decide +kernel
      have hl : raw7577step1Labels = raw7577step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7577step0 raw7577step0Labels permutation56 hz
    mixedMoment B raw7577step1 raw7577step1Labels = mixedMoment B raw7577step2 raw7577step2Labels := by
      have ha : raw7577step2 = (fun i j => raw7577step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7577step2 raw7577step1; decide +kernel
      have hl : raw7577step2Labels = raw7577step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7577step1 raw7577step1Labels permutation31 permutation3
    mixedMoment B raw7577step2 raw7577step2Labels = mixedMoment B raw7577step3 raw7577step3Labels := by
      have ha : raw7577step3 = -raw7577step2 := by apply Matrix.ext; change ∀ i j, raw7577step3 i j = -(raw7577step2 i j); unfold raw7577step3 raw7577step2; decide +kernel
      have hl : raw7577step3Labels = raw7577step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3889 node3889Labels := by rfl

def raw7578 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0]]
def raw7578Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7578step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0]]
def raw7578step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7578step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0]]
def raw7578step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7578step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![1, 1, -2], ![1, -1, 0]]
def raw7578step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7578step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![2, -2, 0]]
def raw7578step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7578 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7578 raw7578Labels = mixedMoment B node4019 node4019Labels := by
  calc
    mixedMoment B raw7578 raw7578Labels = mixedMoment B raw7578step0 raw7578step0Labels := by
      have hz : ∀ j, raw7578 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7578step0 = (fun i j => raw7578 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7578step0 raw7578; decide +kernel
      have hl : raw7578step0Labels = raw7578Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7578 raw7578Labels permutation434 hz
    mixedMoment B raw7578step0 raw7578step0Labels = mixedMoment B raw7578step1 raw7578step1Labels := by
      have hz : ∀ j, raw7578step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7578step1 = (fun i j => raw7578step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7578step1 raw7578step0; decide +kernel
      have hl : raw7578step1Labels = raw7578step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7578step0 raw7578step0Labels permutation80 hz
    mixedMoment B raw7578step1 raw7578step1Labels = mixedMoment B raw7578step2 raw7578step2Labels := by
      have hz : ∀ j, raw7578step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw7578step2 = (fun i j => raw7578step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw7578step2 raw7578step1; decide +kernel
      have hl : raw7578step2Labels = raw7578step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7578step1 raw7578step1Labels permutation14 hz
    mixedMoment B raw7578step2 raw7578step2Labels = mixedMoment B raw7578step3 raw7578step3Labels := by
      have ha : raw7578step3 = (fun i j => raw7578step2 (permutation5 i) (permutation6 j)) := by apply Matrix.ext; unfold raw7578step3 raw7578step2; decide +kernel
      have hl : raw7578step3Labels = raw7578step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7578step2 raw7578step2Labels permutation5 permutation6
    _ = mixedMoment B node4019 node4019Labels := by rfl

def raw7579 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw7579Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7579step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw7579step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7579step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw7579step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7579step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw7579step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7579 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7579 raw7579Labels = mixedMoment B node1294 node1294Labels := by
  calc
    mixedMoment B raw7579 raw7579Labels = mixedMoment B raw7579step0 raw7579step0Labels := by
      have hz : ∀ j, raw7579 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7579step0 = (fun i j => raw7579 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7579step0 raw7579; decide +kernel
      have hl : raw7579step0Labels = raw7579Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7579 raw7579Labels permutation434 hz
    mixedMoment B raw7579step0 raw7579step0Labels = mixedMoment B raw7579step1 raw7579step1Labels := by
      have hz : ∀ j, raw7579step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7579step1 = (fun i j => raw7579step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7579step1 raw7579step0; decide +kernel
      have hl : raw7579step1Labels = raw7579step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7579step0 raw7579step0Labels permutation80 hz
    mixedMoment B raw7579step1 raw7579step1Labels = mixedMoment B raw7579step2 raw7579step2Labels := by
      have ha : raw7579step2 = (fun i j => raw7579step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7579step2 raw7579step1; decide +kernel
      have hl : raw7579step2Labels = raw7579step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7579step1 raw7579step1Labels permutation10 permutation3
    _ = mixedMoment B node1294 node1294Labels := by rfl

def raw7580 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw7580Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7580step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw7580step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7580step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw7580step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7580 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7580 raw7580Labels = mixedMoment B node2954 node2954Labels := by
  calc
    mixedMoment B raw7580 raw7580Labels = mixedMoment B raw7580step0 raw7580step0Labels := by
      have hz : ∀ j, raw7580 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7580step0 = (fun i j => raw7580 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7580step0 raw7580; decide +kernel
      have hl : raw7580step0Labels = raw7580Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7580 raw7580Labels permutation434 hz
    mixedMoment B raw7580step0 raw7580step0Labels = mixedMoment B raw7580step1 raw7580step1Labels := by
      have ha : raw7580step1 = (fun i j => raw7580step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7580step1 raw7580step0; decide +kernel
      have hl : raw7580step1Labels = raw7580step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7580step0 raw7580step0Labels permutation40 permutation3
    _ = mixedMoment B node2954 node2954Labels := by rfl

def raw7581 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw7581Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7581step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw7581step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7581step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw7581step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7581 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7581 raw7581Labels = mixedMoment B node2954 node2954Labels := by
  calc
    mixedMoment B raw7581 raw7581Labels = mixedMoment B raw7581step0 raw7581step0Labels := by
      have hz : ∀ j, raw7581 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7581step0 = (fun i j => raw7581 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7581step0 raw7581; decide +kernel
      have hl : raw7581step0Labels = raw7581Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7581 raw7581Labels permutation346 hz
    mixedMoment B raw7581step0 raw7581step0Labels = mixedMoment B raw7581step1 raw7581step1Labels := by
      have ha : raw7581step1 = (fun i j => raw7581step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7581step1 raw7581step0; decide +kernel
      have hl : raw7581step1Labels = raw7581step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7581step0 raw7581step0Labels permutation40 permutation3
    _ = mixedMoment B node2954 node2954Labels := by rfl

def raw7582 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0]]
def raw7582Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7582step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0]]
def raw7582step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7582step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0]]
def raw7582step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7582step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw7582step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7582 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7582 raw7582Labels = mixedMoment B node3120 node3120Labels := by
  calc
    mixedMoment B raw7582 raw7582Labels = mixedMoment B raw7582step0 raw7582step0Labels := by
      have hz : ∀ j, raw7582 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7582step0 = (fun i j => raw7582 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7582step0 raw7582; decide +kernel
      have hl : raw7582step0Labels = raw7582Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7582 raw7582Labels permutation434 hz
    mixedMoment B raw7582step0 raw7582step0Labels = mixedMoment B raw7582step1 raw7582step1Labels := by
      have hz : ∀ j, raw7582step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7582step1 = (fun i j => raw7582step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7582step1 raw7582step0; decide +kernel
      have hl : raw7582step1Labels = raw7582step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7582step0 raw7582step0Labels permutation80 hz
    mixedMoment B raw7582step1 raw7582step1Labels = mixedMoment B raw7582step2 raw7582step2Labels := by
      have ha : raw7582step2 = (fun i j => raw7582step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7582step2 raw7582step1; decide +kernel
      have hl : raw7582step2Labels = raw7582step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7582step1 raw7582step1Labels permutation10 permutation3
    _ = mixedMoment B node3120 node3120Labels := by rfl

def raw7583 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw7583Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7583step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw7583step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7583step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw7583step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7583step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw7583step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7583 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7583 raw7583Labels = mixedMoment B node1294 node1294Labels := by
  calc
    mixedMoment B raw7583 raw7583Labels = mixedMoment B raw7583step0 raw7583step0Labels := by
      have hz : ∀ j, raw7583 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7583step0 = (fun i j => raw7583 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7583step0 raw7583; decide +kernel
      have hl : raw7583step0Labels = raw7583Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7583 raw7583Labels permutation434 hz
    mixedMoment B raw7583step0 raw7583step0Labels = mixedMoment B raw7583step1 raw7583step1Labels := by
      have hz : ∀ j, raw7583step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7583step1 = (fun i j => raw7583step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7583step1 raw7583step0; decide +kernel
      have hl : raw7583step1Labels = raw7583step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7583step0 raw7583step0Labels permutation56 hz
    mixedMoment B raw7583step1 raw7583step1Labels = mixedMoment B raw7583step2 raw7583step2Labels := by
      have ha : raw7583step2 = (fun i j => raw7583step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7583step2 raw7583step1; decide +kernel
      have hl : raw7583step2Labels = raw7583step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7583step1 raw7583step1Labels permutation10 permutation3
    _ = mixedMoment B node1294 node1294Labels := by rfl

def raw7584 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw7584Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7584step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw7584step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7584step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw7584step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7584 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7584 raw7584Labels = mixedMoment B node2954 node2954Labels := by
  calc
    mixedMoment B raw7584 raw7584Labels = mixedMoment B raw7584step0 raw7584step0Labels := by
      have hz : ∀ j, raw7584 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7584step0 = (fun i j => raw7584 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7584step0 raw7584; decide +kernel
      have hl : raw7584step0Labels = raw7584Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7584 raw7584Labels permutation434 hz
    mixedMoment B raw7584step0 raw7584step0Labels = mixedMoment B raw7584step1 raw7584step1Labels := by
      have ha : raw7584step1 = (fun i j => raw7584step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7584step1 raw7584step0; decide +kernel
      have hl : raw7584step1Labels = raw7584step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7584step0 raw7584step0Labels permutation34 permutation3
    _ = mixedMoment B node2954 node2954Labels := by rfl

def raw7585 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw7585Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7585step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw7585step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7585step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw7585step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7585 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7585 raw7585Labels = mixedMoment B node2954 node2954Labels := by
  calc
    mixedMoment B raw7585 raw7585Labels = mixedMoment B raw7585step0 raw7585step0Labels := by
      have hz : ∀ j, raw7585 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw7585step0 = (fun i j => raw7585 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw7585step0 raw7585; decide +kernel
      have hl : raw7585step0Labels = raw7585Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7585 raw7585Labels permutation265 hz
    mixedMoment B raw7585step0 raw7585step0Labels = mixedMoment B raw7585step1 raw7585step1Labels := by
      have ha : raw7585step1 = (fun i j => raw7585step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7585step1 raw7585step0; decide +kernel
      have hl : raw7585step1Labels = raw7585step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7585step0 raw7585step0Labels permutation40 permutation3
    _ = mixedMoment B node2954 node2954Labels := by rfl

def raw7586 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0]]
def raw7586Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7586step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0]]
def raw7586step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7586step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0]]
def raw7586step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7586step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw7586step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7586 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7586 raw7586Labels = mixedMoment B node3120 node3120Labels := by
  calc
    mixedMoment B raw7586 raw7586Labels = mixedMoment B raw7586step0 raw7586step0Labels := by
      have hz : ∀ j, raw7586 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7586step0 = (fun i j => raw7586 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7586step0 raw7586; decide +kernel
      have hl : raw7586step0Labels = raw7586Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7586 raw7586Labels permutation434 hz
    mixedMoment B raw7586step0 raw7586step0Labels = mixedMoment B raw7586step1 raw7586step1Labels := by
      have hz : ∀ j, raw7586step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7586step1 = (fun i j => raw7586step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7586step1 raw7586step0; decide +kernel
      have hl : raw7586step1Labels = raw7586step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7586step0 raw7586step0Labels permutation56 hz
    mixedMoment B raw7586step1 raw7586step1Labels = mixedMoment B raw7586step2 raw7586step2Labels := by
      have ha : raw7586step2 = (fun i j => raw7586step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7586step2 raw7586step1; decide +kernel
      have hl : raw7586step2Labels = raw7586step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7586step1 raw7586step1Labels permutation10 permutation3
    _ = mixedMoment B node3120 node3120Labels := by rfl

def raw7587 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw7587Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7587step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw7587step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7587step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw7587step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7587step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw7587step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7587 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7587 raw7587Labels = mixedMoment B node1294 node1294Labels := by
  calc
    mixedMoment B raw7587 raw7587Labels = mixedMoment B raw7587step0 raw7587step0Labels := by
      have hz : ∀ j, raw7587 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7587step0 = (fun i j => raw7587 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7587step0 raw7587; decide +kernel
      have hl : raw7587step0Labels = raw7587Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7587 raw7587Labels permutation346 hz
    mixedMoment B raw7587step0 raw7587step0Labels = mixedMoment B raw7587step1 raw7587step1Labels := by
      have hz : ∀ j, raw7587step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7587step1 = (fun i j => raw7587step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7587step1 raw7587step0; decide +kernel
      have hl : raw7587step1Labels = raw7587step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7587step0 raw7587step0Labels permutation56 hz
    mixedMoment B raw7587step1 raw7587step1Labels = mixedMoment B raw7587step2 raw7587step2Labels := by
      have ha : raw7587step2 = (fun i j => raw7587step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7587step2 raw7587step1; decide +kernel
      have hl : raw7587step2Labels = raw7587step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7587step1 raw7587step1Labels permutation10 permutation3
    _ = mixedMoment B node1294 node1294Labels := by rfl

def raw7588 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw7588Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7588step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw7588step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7588step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw7588step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7588 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7588 raw7588Labels = mixedMoment B node2954 node2954Labels := by
  calc
    mixedMoment B raw7588 raw7588Labels = mixedMoment B raw7588step0 raw7588step0Labels := by
      have hz : ∀ j, raw7588 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7588step0 = (fun i j => raw7588 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7588step0 raw7588; decide +kernel
      have hl : raw7588step0Labels = raw7588Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7588 raw7588Labels permutation346 hz
    mixedMoment B raw7588step0 raw7588step0Labels = mixedMoment B raw7588step1 raw7588step1Labels := by
      have ha : raw7588step1 = (fun i j => raw7588step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7588step1 raw7588step0; decide +kernel
      have hl : raw7588step1Labels = raw7588step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7588step0 raw7588step0Labels permutation34 permutation3
    _ = mixedMoment B node2954 node2954Labels := by rfl

def raw7589 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw7589Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7589step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw7589step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7589step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw7589step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7589 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7589 raw7589Labels = mixedMoment B node2954 node2954Labels := by
  calc
    mixedMoment B raw7589 raw7589Labels = mixedMoment B raw7589step0 raw7589step0Labels := by
      have hz : ∀ j, raw7589 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw7589step0 = (fun i j => raw7589 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw7589step0 raw7589; decide +kernel
      have hl : raw7589step0Labels = raw7589Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7589 raw7589Labels permutation265 hz
    mixedMoment B raw7589step0 raw7589step0Labels = mixedMoment B raw7589step1 raw7589step1Labels := by
      have ha : raw7589step1 = (fun i j => raw7589step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7589step1 raw7589step0; decide +kernel
      have hl : raw7589step1Labels = raw7589step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7589step0 raw7589step0Labels permutation34 permutation3
    _ = mixedMoment B node2954 node2954Labels := by rfl

def raw7590 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0]]
def raw7590Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7590step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0]]
def raw7590step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7590step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0]]
def raw7590step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7590step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw7590step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7590 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7590 raw7590Labels = mixedMoment B node3120 node3120Labels := by
  calc
    mixedMoment B raw7590 raw7590Labels = mixedMoment B raw7590step0 raw7590step0Labels := by
      have hz : ∀ j, raw7590 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7590step0 = (fun i j => raw7590 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7590step0 raw7590; decide +kernel
      have hl : raw7590step0Labels = raw7590Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7590 raw7590Labels permutation346 hz
    mixedMoment B raw7590step0 raw7590step0Labels = mixedMoment B raw7590step1 raw7590step1Labels := by
      have hz : ∀ j, raw7590step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7590step1 = (fun i j => raw7590step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7590step1 raw7590step0; decide +kernel
      have hl : raw7590step1Labels = raw7590step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7590step0 raw7590step0Labels permutation56 hz
    mixedMoment B raw7590step1 raw7590step1Labels = mixedMoment B raw7590step2 raw7590step2Labels := by
      have ha : raw7590step2 = (fun i j => raw7590step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7590step2 raw7590step1; decide +kernel
      have hl : raw7590step2Labels = raw7590step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7590step1 raw7590step1Labels permutation10 permutation3
    _ = mixedMoment B node3120 node3120Labels := by rfl

def raw7591 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw7591Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7591step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw7591step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7591step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw7591step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7591step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![2, 0, -2], ![2, -2, 0]]
def raw7591step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7591step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -2, 0], ![2, 0, -2]]
def raw7591step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7591 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7591 raw7591Labels = mixedMoment B node1311 node1311Labels := by
  calc
    mixedMoment B raw7591 raw7591Labels = mixedMoment B raw7591step0 raw7591step0Labels := by
      have hz : ∀ j, raw7591 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7591step0 = (fun i j => raw7591 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7591step0 raw7591; decide +kernel
      have hl : raw7591step0Labels = raw7591Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7591 raw7591Labels permutation434 hz
    mixedMoment B raw7591step0 raw7591step0Labels = mixedMoment B raw7591step1 raw7591step1Labels := by
      have hz : ∀ j, raw7591step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7591step1 = (fun i j => raw7591step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7591step1 raw7591step0; decide +kernel
      have hl : raw7591step1Labels = raw7591step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7591step0 raw7591step0Labels permutation80 hz
    mixedMoment B raw7591step1 raw7591step1Labels = mixedMoment B raw7591step2 raw7591step2Labels := by
      have hz : ∀ j, raw7591step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw7591step2 = (fun i j => raw7591step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw7591step2 raw7591step1; decide +kernel
      have hl : raw7591step2Labels = raw7591step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7591step1 raw7591step1Labels permutation14 hz
    mixedMoment B raw7591step2 raw7591step2Labels = mixedMoment B raw7591step3 raw7591step3Labels := by
      have ha : raw7591step3 = (fun i j => raw7591step2 (permutation2 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7591step3 raw7591step2; decide +kernel
      have hl : raw7591step3Labels = raw7591step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7591step2 raw7591step2Labels permutation2 permutation3
    _ = mixedMoment B node1311 node1311Labels := by rfl

def raw7592 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw7592Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7592step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw7592step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7592step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw7592step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7592step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -2, 0], ![2, 0, -2]]
def raw7592step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7592 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7592 raw7592Labels = mixedMoment B node2968 node2968Labels := by
  calc
    mixedMoment B raw7592 raw7592Labels = mixedMoment B raw7592step0 raw7592step0Labels := by
      have hz : ∀ j, raw7592 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7592step0 = (fun i j => raw7592 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7592step0 raw7592; decide +kernel
      have hl : raw7592step0Labels = raw7592Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7592 raw7592Labels permutation434 hz
    mixedMoment B raw7592step0 raw7592step0Labels = mixedMoment B raw7592step1 raw7592step1Labels := by
      have hz : ∀ j, raw7592step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7592step1 = (fun i j => raw7592step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7592step1 raw7592step0; decide +kernel
      have hl : raw7592step1Labels = raw7592step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7592step0 raw7592step0Labels permutation80 hz
    mixedMoment B raw7592step1 raw7592step1Labels = mixedMoment B raw7592step2 raw7592step2Labels := by
      have ha : raw7592step2 = (fun i j => raw7592step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7592step2 raw7592step1; decide +kernel
      have hl : raw7592step2Labels = raw7592step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7592step1 raw7592step1Labels permutation8 permutation3
    _ = mixedMoment B node2968 node2968Labels := by rfl

def raw7593 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw7593Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7593step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw7593step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7593step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw7593step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7593step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -2, 0], ![2, 0, -2]]
def raw7593step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7593 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7593 raw7593Labels = mixedMoment B node2968 node2968Labels := by
  calc
    mixedMoment B raw7593 raw7593Labels = mixedMoment B raw7593step0 raw7593step0Labels := by
      have hz : ∀ j, raw7593 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7593step0 = (fun i j => raw7593 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7593step0 raw7593; decide +kernel
      have hl : raw7593step0Labels = raw7593Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7593 raw7593Labels permutation434 hz
    mixedMoment B raw7593step0 raw7593step0Labels = mixedMoment B raw7593step1 raw7593step1Labels := by
      have hz : ∀ j, raw7593step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7593step1 = (fun i j => raw7593step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7593step1 raw7593step0; decide +kernel
      have hl : raw7593step1Labels = raw7593step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7593step0 raw7593step0Labels permutation56 hz
    mixedMoment B raw7593step1 raw7593step1Labels = mixedMoment B raw7593step2 raw7593step2Labels := by
      have ha : raw7593step2 = (fun i j => raw7593step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7593step2 raw7593step1; decide +kernel
      have hl : raw7593step2Labels = raw7593step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7593step1 raw7593step1Labels permutation8 permutation3
    _ = mixedMoment B node2968 node2968Labels := by rfl

def raw7594 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw7594Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7594step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw7594step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7594step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw7594step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7594step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -2, 0], ![2, 0, -2]]
def raw7594step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7594 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7594 raw7594Labels = mixedMoment B node2968 node2968Labels := by
  calc
    mixedMoment B raw7594 raw7594Labels = mixedMoment B raw7594step0 raw7594step0Labels := by
      have hz : ∀ j, raw7594 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7594step0 = (fun i j => raw7594 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7594step0 raw7594; decide +kernel
      have hl : raw7594step0Labels = raw7594Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7594 raw7594Labels permutation346 hz
    mixedMoment B raw7594step0 raw7594step0Labels = mixedMoment B raw7594step1 raw7594step1Labels := by
      have hz : ∀ j, raw7594step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7594step1 = (fun i j => raw7594step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7594step1 raw7594step0; decide +kernel
      have hl : raw7594step1Labels = raw7594step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7594step0 raw7594step0Labels permutation56 hz
    mixedMoment B raw7594step1 raw7594step1Labels = mixedMoment B raw7594step2 raw7594step2Labels := by
      have ha : raw7594step2 = (fun i j => raw7594step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7594step2 raw7594step1; decide +kernel
      have hl : raw7594step2Labels = raw7594step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7594step1 raw7594step1Labels permutation8 permutation3
    _ = mixedMoment B node2968 node2968Labels := by rfl

def raw7595 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw7595Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7595step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw7595step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7595step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw7595step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7595step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![2, 0, -2], ![1, -1, 0]]
def raw7595step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7595step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![2, -2, 0]]
def raw7595step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7595 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7595 raw7595Labels = mixedMoment B node3124 node3124Labels := by
  calc
    mixedMoment B raw7595 raw7595Labels = mixedMoment B raw7595step0 raw7595step0Labels := by
      have hz : ∀ j, raw7595 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7595step0 = (fun i j => raw7595 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7595step0 raw7595; decide +kernel
      have hl : raw7595step0Labels = raw7595Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7595 raw7595Labels permutation434 hz
    mixedMoment B raw7595step0 raw7595step0Labels = mixedMoment B raw7595step1 raw7595step1Labels := by
      have hz : ∀ j, raw7595step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7595step1 = (fun i j => raw7595step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7595step1 raw7595step0; decide +kernel
      have hl : raw7595step1Labels = raw7595step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7595step0 raw7595step0Labels permutation80 hz
    mixedMoment B raw7595step1 raw7595step1Labels = mixedMoment B raw7595step2 raw7595step2Labels := by
      have hz : ∀ j, raw7595step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw7595step2 = (fun i j => raw7595step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw7595step2 raw7595step1; decide +kernel
      have hl : raw7595step2Labels = raw7595step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7595step1 raw7595step1Labels permutation14 hz
    mixedMoment B raw7595step2 raw7595step2Labels = mixedMoment B raw7595step3 raw7595step3Labels := by
      have ha : raw7595step3 = (fun i j => raw7595step2 (permutation3 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7595step3 raw7595step2; decide +kernel
      have hl : raw7595step3Labels = raw7595step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7595step2 raw7595step2Labels permutation3 permutation3
    _ = mixedMoment B node3124 node3124Labels := by rfl

def raw7596 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![3, -3, 0]]
def raw7596Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7596step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![3, -3, 0]]
def raw7596step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7596step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 2, -2], ![3, -3, 0]]
def raw7596step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7596step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![3, -3, 0]]
def raw7596step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7596step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-3, 2, 1]]
def raw7596step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7596step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![3, -2, -1]]
def raw7596step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7596 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7596 raw7596Labels = mixedMoment B node2281 node2281Labels := by
  calc
    mixedMoment B raw7596 raw7596Labels = mixedMoment B raw7596step0 raw7596step0Labels := by
      have hz : ∀ j, raw7596 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7596step0 = (fun i j => raw7596 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7596step0 raw7596; decide +kernel
      have hl : raw7596step0Labels = raw7596Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7596 raw7596Labels permutation434 hz
    mixedMoment B raw7596step0 raw7596step0Labels = mixedMoment B raw7596step1 raw7596step1Labels := by
      have hz : ∀ j, raw7596step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7596step1 = (fun i j => raw7596step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7596step1 raw7596step0; decide +kernel
      have hl : raw7596step1Labels = raw7596step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7596step0 raw7596step0Labels permutation80 hz
    mixedMoment B raw7596step1 raw7596step1Labels = mixedMoment B raw7596step2 raw7596step2Labels := by
      have hz : ∀ j, raw7596step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw7596step2 = (fun i j => raw7596step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw7596step2 raw7596step1; decide +kernel
      have hl : raw7596step2Labels = raw7596step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7596step1 raw7596step1Labels permutation14 hz
    mixedMoment B raw7596step2 raw7596step2Labels = mixedMoment B raw7596step3 raw7596step3Labels := by
      have ha : raw7596step3 = (fun i j => raw7596step2 (permutation7 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7596step3 raw7596step2; decide +kernel
      have hl : raw7596step3Labels = raw7596step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7596step2 raw7596step2Labels permutation7 permutation3
    mixedMoment B raw7596step3 raw7596step3Labels = mixedMoment B raw7596step4 raw7596step4Labels := by
      have ha : raw7596step4 = -raw7596step3 := by apply Matrix.ext; change ∀ i j, raw7596step4 i j = -(raw7596step3 i j); unfold raw7596step4 raw7596step3; decide +kernel
      have hl : raw7596step4Labels = raw7596step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2281 node2281Labels := by rfl

def raw7597 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw7597Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7597step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw7597step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7597step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw7597step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7597step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw7597step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7597step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw7597step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7597 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7597 raw7597Labels = mixedMoment B node4503 node4503Labels := by
  calc
    mixedMoment B raw7597 raw7597Labels = mixedMoment B raw7597step0 raw7597step0Labels := by
      have hz : ∀ j, raw7597 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7597step0 = (fun i j => raw7597 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7597step0 raw7597; decide +kernel
      have hl : raw7597step0Labels = raw7597Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7597 raw7597Labels permutation434 hz
    mixedMoment B raw7597step0 raw7597step0Labels = mixedMoment B raw7597step1 raw7597step1Labels := by
      have hz : ∀ j, raw7597step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7597step1 = (fun i j => raw7597step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7597step1 raw7597step0; decide +kernel
      have hl : raw7597step1Labels = raw7597step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7597step0 raw7597step0Labels permutation80 hz
    mixedMoment B raw7597step1 raw7597step1Labels = mixedMoment B raw7597step2 raw7597step2Labels := by
      have ha : raw7597step2 = (fun i j => raw7597step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7597step2 raw7597step1; decide +kernel
      have hl : raw7597step2Labels = raw7597step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7597step1 raw7597step1Labels permutation8 permutation3
    mixedMoment B raw7597step2 raw7597step2Labels = mixedMoment B raw7597step3 raw7597step3Labels := by
      have ha : raw7597step3 = raw7597step2 := by apply Matrix.ext; unfold raw7597step3 raw7597step2; decide +kernel
      have hl : raw7597step2Labels = labelEmbedding6 ∘ raw7597step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7597step2 raw7597step2Labels raw7597step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4503 node4503Labels := by rfl

def raw7598 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw7598Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7598step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw7598step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7598step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw7598step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7598step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw7598step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7598 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7598 raw7598Labels = mixedMoment B node5105 node5105Labels := by
  calc
    mixedMoment B raw7598 raw7598Labels = mixedMoment B raw7598step0 raw7598step0Labels := by
      have hz : ∀ j, raw7598 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7598step0 = (fun i j => raw7598 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7598step0 raw7598; decide +kernel
      have hl : raw7598step0Labels = raw7598Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7598 raw7598Labels permutation434 hz
    mixedMoment B raw7598step0 raw7598step0Labels = mixedMoment B raw7598step1 raw7598step1Labels := by
      have ha : raw7598step1 = (fun i j => raw7598step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7598step1 raw7598step0; decide +kernel
      have hl : raw7598step1Labels = raw7598step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7598step0 raw7598step0Labels permutation38 permutation3
    mixedMoment B raw7598step1 raw7598step1Labels = mixedMoment B raw7598step2 raw7598step2Labels := by
      have ha : raw7598step2 = raw7598step1 := by apply Matrix.ext; unfold raw7598step2 raw7598step1; decide +kernel
      have hl : raw7598step1Labels = labelEmbedding6 ∘ raw7598step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7598step1 raw7598step1Labels raw7598step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5105 node5105Labels := by rfl

def raw7599 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw7599Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7599step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw7599step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7599step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw7599step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7599step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw7599step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7599 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7599 raw7599Labels = mixedMoment B node5105 node5105Labels := by
  calc
    mixedMoment B raw7599 raw7599Labels = mixedMoment B raw7599step0 raw7599step0Labels := by
      have hz : ∀ j, raw7599 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7599step0 = (fun i j => raw7599 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7599step0 raw7599; decide +kernel
      have hl : raw7599step0Labels = raw7599Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7599 raw7599Labels permutation346 hz
    mixedMoment B raw7599step0 raw7599step0Labels = mixedMoment B raw7599step1 raw7599step1Labels := by
      have ha : raw7599step1 = (fun i j => raw7599step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7599step1 raw7599step0; decide +kernel
      have hl : raw7599step1Labels = raw7599step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7599step0 raw7599step0Labels permutation38 permutation3
    mixedMoment B raw7599step1 raw7599step1Labels = mixedMoment B raw7599step2 raw7599step2Labels := by
      have ha : raw7599step2 = raw7599step1 := by apply Matrix.ext; unfold raw7599step2 raw7599step1; decide +kernel
      have hl : raw7599step1Labels = labelEmbedding6 ∘ raw7599step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7599step1 raw7599step1Labels raw7599step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5105 node5105Labels := by rfl

def raw7600 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw7600Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7600step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw7600step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7600step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw7600step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7600step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw7600step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7600step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw7600step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7600 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7600 raw7600Labels = mixedMoment B node4503 node4503Labels := by
  calc
    mixedMoment B raw7600 raw7600Labels = mixedMoment B raw7600step0 raw7600step0Labels := by
      have hz : ∀ j, raw7600 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7600step0 = (fun i j => raw7600 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7600step0 raw7600; decide +kernel
      have hl : raw7600step0Labels = raw7600Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7600 raw7600Labels permutation434 hz
    mixedMoment B raw7600step0 raw7600step0Labels = mixedMoment B raw7600step1 raw7600step1Labels := by
      have hz : ∀ j, raw7600step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7600step1 = (fun i j => raw7600step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7600step1 raw7600step0; decide +kernel
      have hl : raw7600step1Labels = raw7600step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7600step0 raw7600step0Labels permutation56 hz
    mixedMoment B raw7600step1 raw7600step1Labels = mixedMoment B raw7600step2 raw7600step2Labels := by
      have ha : raw7600step2 = (fun i j => raw7600step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7600step2 raw7600step1; decide +kernel
      have hl : raw7600step2Labels = raw7600step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7600step1 raw7600step1Labels permutation8 permutation3
    mixedMoment B raw7600step2 raw7600step2Labels = mixedMoment B raw7600step3 raw7600step3Labels := by
      have ha : raw7600step3 = raw7600step2 := by apply Matrix.ext; unfold raw7600step3 raw7600step2; decide +kernel
      have hl : raw7600step2Labels = labelEmbedding6 ∘ raw7600step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7600step2 raw7600step2Labels raw7600step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4503 node4503Labels := by rfl

def raw7601 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw7601Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7601step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw7601step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7601step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw7601step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7601step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw7601step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7601 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7601 raw7601Labels = mixedMoment B node5105 node5105Labels := by
  calc
    mixedMoment B raw7601 raw7601Labels = mixedMoment B raw7601step0 raw7601step0Labels := by
      have hz : ∀ j, raw7601 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7601step0 = (fun i j => raw7601 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7601step0 raw7601; decide +kernel
      have hl : raw7601step0Labels = raw7601Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7601 raw7601Labels permutation434 hz
    mixedMoment B raw7601step0 raw7601step0Labels = mixedMoment B raw7601step1 raw7601step1Labels := by
      have ha : raw7601step1 = (fun i j => raw7601step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7601step1 raw7601step0; decide +kernel
      have hl : raw7601step1Labels = raw7601step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7601step0 raw7601step0Labels permutation32 permutation3
    mixedMoment B raw7601step1 raw7601step1Labels = mixedMoment B raw7601step2 raw7601step2Labels := by
      have ha : raw7601step2 = raw7601step1 := by apply Matrix.ext; unfold raw7601step2 raw7601step1; decide +kernel
      have hl : raw7601step1Labels = labelEmbedding6 ∘ raw7601step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7601step1 raw7601step1Labels raw7601step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5105 node5105Labels := by rfl

def raw7602 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw7602Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7602step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw7602step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7602step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw7602step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7602step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw7602step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7602 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7602 raw7602Labels = mixedMoment B node5105 node5105Labels := by
  calc
    mixedMoment B raw7602 raw7602Labels = mixedMoment B raw7602step0 raw7602step0Labels := by
      have hz : ∀ j, raw7602 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw7602step0 = (fun i j => raw7602 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw7602step0 raw7602; decide +kernel
      have hl : raw7602step0Labels = raw7602Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7602 raw7602Labels permutation265 hz
    mixedMoment B raw7602step0 raw7602step0Labels = mixedMoment B raw7602step1 raw7602step1Labels := by
      have ha : raw7602step1 = (fun i j => raw7602step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7602step1 raw7602step0; decide +kernel
      have hl : raw7602step1Labels = raw7602step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7602step0 raw7602step0Labels permutation38 permutation3
    mixedMoment B raw7602step1 raw7602step1Labels = mixedMoment B raw7602step2 raw7602step2Labels := by
      have ha : raw7602step2 = raw7602step1 := by apply Matrix.ext; unfold raw7602step2 raw7602step1; decide +kernel
      have hl : raw7602step1Labels = labelEmbedding6 ∘ raw7602step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7602step1 raw7602step1Labels raw7602step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5105 node5105Labels := by rfl

def raw7603 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw7603Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7603step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw7603step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7603step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw7603step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7603step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw7603step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7603step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw7603step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7603 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7603 raw7603Labels = mixedMoment B node4503 node4503Labels := by
  calc
    mixedMoment B raw7603 raw7603Labels = mixedMoment B raw7603step0 raw7603step0Labels := by
      have hz : ∀ j, raw7603 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7603step0 = (fun i j => raw7603 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7603step0 raw7603; decide +kernel
      have hl : raw7603step0Labels = raw7603Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7603 raw7603Labels permutation346 hz
    mixedMoment B raw7603step0 raw7603step0Labels = mixedMoment B raw7603step1 raw7603step1Labels := by
      have hz : ∀ j, raw7603step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7603step1 = (fun i j => raw7603step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7603step1 raw7603step0; decide +kernel
      have hl : raw7603step1Labels = raw7603step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7603step0 raw7603step0Labels permutation56 hz
    mixedMoment B raw7603step1 raw7603step1Labels = mixedMoment B raw7603step2 raw7603step2Labels := by
      have ha : raw7603step2 = (fun i j => raw7603step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7603step2 raw7603step1; decide +kernel
      have hl : raw7603step2Labels = raw7603step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7603step1 raw7603step1Labels permutation8 permutation3
    mixedMoment B raw7603step2 raw7603step2Labels = mixedMoment B raw7603step3 raw7603step3Labels := by
      have ha : raw7603step3 = raw7603step2 := by apply Matrix.ext; unfold raw7603step3 raw7603step2; decide +kernel
      have hl : raw7603step2Labels = labelEmbedding6 ∘ raw7603step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7603step2 raw7603step2Labels raw7603step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4503 node4503Labels := by rfl

def raw7604 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw7604Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7604step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw7604step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7604step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw7604step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7604step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw7604step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7604 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7604 raw7604Labels = mixedMoment B node5105 node5105Labels := by
  calc
    mixedMoment B raw7604 raw7604Labels = mixedMoment B raw7604step0 raw7604step0Labels := by
      have hz : ∀ j, raw7604 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7604step0 = (fun i j => raw7604 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7604step0 raw7604; decide +kernel
      have hl : raw7604step0Labels = raw7604Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7604 raw7604Labels permutation346 hz
    mixedMoment B raw7604step0 raw7604step0Labels = mixedMoment B raw7604step1 raw7604step1Labels := by
      have ha : raw7604step1 = (fun i j => raw7604step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7604step1 raw7604step0; decide +kernel
      have hl : raw7604step1Labels = raw7604step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7604step0 raw7604step0Labels permutation32 permutation3
    mixedMoment B raw7604step1 raw7604step1Labels = mixedMoment B raw7604step2 raw7604step2Labels := by
      have ha : raw7604step2 = raw7604step1 := by apply Matrix.ext; unfold raw7604step2 raw7604step1; decide +kernel
      have hl : raw7604step1Labels = labelEmbedding6 ∘ raw7604step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7604step1 raw7604step1Labels raw7604step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5105 node5105Labels := by rfl

def raw7605 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw7605Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7605step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw7605step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7605step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw7605step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7605step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw7605step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7605 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7605 raw7605Labels = mixedMoment B node5105 node5105Labels := by
  calc
    mixedMoment B raw7605 raw7605Labels = mixedMoment B raw7605step0 raw7605step0Labels := by
      have hz : ∀ j, raw7605 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw7605step0 = (fun i j => raw7605 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw7605step0 raw7605; decide +kernel
      have hl : raw7605step0Labels = raw7605Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7605 raw7605Labels permutation265 hz
    mixedMoment B raw7605step0 raw7605step0Labels = mixedMoment B raw7605step1 raw7605step1Labels := by
      have ha : raw7605step1 = (fun i j => raw7605step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7605step1 raw7605step0; decide +kernel
      have hl : raw7605step1Labels = raw7605step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7605step0 raw7605step0Labels permutation32 permutation3
    mixedMoment B raw7605step1 raw7605step1Labels = mixedMoment B raw7605step2 raw7605step2Labels := by
      have ha : raw7605step2 = raw7605step1 := by apply Matrix.ext; unfold raw7605step2 raw7605step1; decide +kernel
      have hl : raw7605step1Labels = labelEmbedding6 ∘ raw7605step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7605step1 raw7605step1Labels raw7605step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5105 node5105Labels := by rfl

def raw7606 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![2, 0, -2]]
def raw7606Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7606step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![2, 0, -2]]
def raw7606step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7606step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![2, -3, 1], ![2, 0, -2]]
def raw7606step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7606step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 3, 1], ![2, -3, 1], ![2, 0, -2]]
def raw7606step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7606step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -2, 0], ![2, 1, -3]]
def raw7606step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7606step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -2, 0], ![2, 1, -3]]
def raw7606step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7606 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7606 raw7606Labels = mixedMoment B node4510 node4510Labels := by
  calc
    mixedMoment B raw7606 raw7606Labels = mixedMoment B raw7606step0 raw7606step0Labels := by
      have hz : ∀ j, raw7606 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7606step0 = (fun i j => raw7606 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7606step0 raw7606; decide +kernel
      have hl : raw7606step0Labels = raw7606Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7606 raw7606Labels permutation434 hz
    mixedMoment B raw7606step0 raw7606step0Labels = mixedMoment B raw7606step1 raw7606step1Labels := by
      have hz : ∀ j, raw7606step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7606step1 = (fun i j => raw7606step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7606step1 raw7606step0; decide +kernel
      have hl : raw7606step1Labels = raw7606step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7606step0 raw7606step0Labels permutation80 hz
    mixedMoment B raw7606step1 raw7606step1Labels = mixedMoment B raw7606step2 raw7606step2Labels := by
      have hz : ∀ j, raw7606step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw7606step2 = (fun i j => raw7606step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw7606step2 raw7606step1; decide +kernel
      have hl : raw7606step2Labels = raw7606step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7606step1 raw7606step1Labels permutation14 hz
    mixedMoment B raw7606step2 raw7606step2Labels = mixedMoment B raw7606step3 raw7606step3Labels := by
      have ha : raw7606step3 = (fun i j => raw7606step2 (permutation3 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7606step3 raw7606step2; decide +kernel
      have hl : raw7606step3Labels = raw7606step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7606step2 raw7606step2Labels permutation3 permutation3
    mixedMoment B raw7606step3 raw7606step3Labels = mixedMoment B raw7606step4 raw7606step4Labels := by
      have ha : raw7606step4 = raw7606step3 := by apply Matrix.ext; unfold raw7606step4 raw7606step3; decide +kernel
      have hl : raw7606step3Labels = labelEmbedding6 ∘ raw7606step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7606step3 raw7606step3Labels raw7606step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4510 node4510Labels := by rfl

def raw7607 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![2, 0, -2]]
def raw7607Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7607step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![2, 0, -2]]
def raw7607step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7607step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![2, -3, 1], ![2, 0, -2]]
def raw7607step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7607step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw7607step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7607step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw7607step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7607 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7607 raw7607Labels = mixedMoment B node5110 node5110Labels := by
  calc
    mixedMoment B raw7607 raw7607Labels = mixedMoment B raw7607step0 raw7607step0Labels := by
      have hz : ∀ j, raw7607 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7607step0 = (fun i j => raw7607 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7607step0 raw7607; decide +kernel
      have hl : raw7607step0Labels = raw7607Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7607 raw7607Labels permutation434 hz
    mixedMoment B raw7607step0 raw7607step0Labels = mixedMoment B raw7607step1 raw7607step1Labels := by
      have hz : ∀ j, raw7607step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7607step1 = (fun i j => raw7607step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7607step1 raw7607step0; decide +kernel
      have hl : raw7607step1Labels = raw7607step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7607step0 raw7607step0Labels permutation80 hz
    mixedMoment B raw7607step1 raw7607step1Labels = mixedMoment B raw7607step2 raw7607step2Labels := by
      have ha : raw7607step2 = (fun i j => raw7607step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7607step2 raw7607step1; decide +kernel
      have hl : raw7607step2Labels = raw7607step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7607step1 raw7607step1Labels permutation9 permutation3
    mixedMoment B raw7607step2 raw7607step2Labels = mixedMoment B raw7607step3 raw7607step3Labels := by
      have ha : raw7607step3 = raw7607step2 := by apply Matrix.ext; unfold raw7607step3 raw7607step2; decide +kernel
      have hl : raw7607step2Labels = labelEmbedding6 ∘ raw7607step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7607step2 raw7607step2Labels raw7607step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5110 node5110Labels := by rfl

def raw7608 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![2, 0, -2]]
def raw7608Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7608step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![2, 0, -2]]
def raw7608step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7608step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![2, -3, 1], ![2, 0, -2]]
def raw7608step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7608step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw7608step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7608step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw7608step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7608 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7608 raw7608Labels = mixedMoment B node5110 node5110Labels := by
  calc
    mixedMoment B raw7608 raw7608Labels = mixedMoment B raw7608step0 raw7608step0Labels := by
      have hz : ∀ j, raw7608 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7608step0 = (fun i j => raw7608 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7608step0 raw7608; decide +kernel
      have hl : raw7608step0Labels = raw7608Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7608 raw7608Labels permutation434 hz
    mixedMoment B raw7608step0 raw7608step0Labels = mixedMoment B raw7608step1 raw7608step1Labels := by
      have hz : ∀ j, raw7608step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7608step1 = (fun i j => raw7608step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7608step1 raw7608step0; decide +kernel
      have hl : raw7608step1Labels = raw7608step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7608step0 raw7608step0Labels permutation56 hz
    mixedMoment B raw7608step1 raw7608step1Labels = mixedMoment B raw7608step2 raw7608step2Labels := by
      have ha : raw7608step2 = (fun i j => raw7608step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7608step2 raw7608step1; decide +kernel
      have hl : raw7608step2Labels = raw7608step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7608step1 raw7608step1Labels permutation9 permutation3
    mixedMoment B raw7608step2 raw7608step2Labels = mixedMoment B raw7608step3 raw7608step3Labels := by
      have ha : raw7608step3 = raw7608step2 := by apply Matrix.ext; unfold raw7608step3 raw7608step2; decide +kernel
      have hl : raw7608step2Labels = labelEmbedding6 ∘ raw7608step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7608step2 raw7608step2Labels raw7608step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5110 node5110Labels := by rfl

def raw7609 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![2, 0, -2]]
def raw7609Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7609step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![2, 0, -2]]
def raw7609step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7609step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![2, -3, 1], ![2, 0, -2]]
def raw7609step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7609step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw7609step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7609step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw7609step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7609 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7609 raw7609Labels = mixedMoment B node5110 node5110Labels := by
  calc
    mixedMoment B raw7609 raw7609Labels = mixedMoment B raw7609step0 raw7609step0Labels := by
      have hz : ∀ j, raw7609 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7609step0 = (fun i j => raw7609 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7609step0 raw7609; decide +kernel
      have hl : raw7609step0Labels = raw7609Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7609 raw7609Labels permutation346 hz
    mixedMoment B raw7609step0 raw7609step0Labels = mixedMoment B raw7609step1 raw7609step1Labels := by
      have hz : ∀ j, raw7609step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7609step1 = (fun i j => raw7609step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7609step1 raw7609step0; decide +kernel
      have hl : raw7609step1Labels = raw7609step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7609step0 raw7609step0Labels permutation56 hz
    mixedMoment B raw7609step1 raw7609step1Labels = mixedMoment B raw7609step2 raw7609step2Labels := by
      have ha : raw7609step2 = (fun i j => raw7609step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7609step2 raw7609step1; decide +kernel
      have hl : raw7609step2Labels = raw7609step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7609step1 raw7609step1Labels permutation9 permutation3
    mixedMoment B raw7609step2 raw7609step2Labels = mixedMoment B raw7609step3 raw7609step3Labels := by
      have ha : raw7609step3 = raw7609step2 := by apply Matrix.ext; unfold raw7609step3 raw7609step2; decide +kernel
      have hl : raw7609step2Labels = labelEmbedding6 ∘ raw7609step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7609step2 raw7609step2Labels raw7609step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5110 node5110Labels := by rfl

def raw7610 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw7610Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7610step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw7610step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7610step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw7610step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7610step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![3, -1, -2]]
def raw7610step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7610step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![3, -2, -1]]
def raw7610step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7610step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![3, -2, -1]]
def raw7610step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7610 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7610 raw7610Labels = mixedMoment B node4507 node4507Labels := by
  calc
    mixedMoment B raw7610 raw7610Labels = mixedMoment B raw7610step0 raw7610step0Labels := by
      have hz : ∀ j, raw7610 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7610step0 = (fun i j => raw7610 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7610step0 raw7610; decide +kernel
      have hl : raw7610step0Labels = raw7610Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7610 raw7610Labels permutation434 hz
    mixedMoment B raw7610step0 raw7610step0Labels = mixedMoment B raw7610step1 raw7610step1Labels := by
      have hz : ∀ j, raw7610step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7610step1 = (fun i j => raw7610step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7610step1 raw7610step0; decide +kernel
      have hl : raw7610step1Labels = raw7610step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7610step0 raw7610step0Labels permutation80 hz
    mixedMoment B raw7610step1 raw7610step1Labels = mixedMoment B raw7610step2 raw7610step2Labels := by
      have hz : ∀ j, raw7610step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw7610step2 = (fun i j => raw7610step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw7610step2 raw7610step1; decide +kernel
      have hl : raw7610step2Labels = raw7610step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7610step1 raw7610step1Labels permutation14 hz
    mixedMoment B raw7610step2 raw7610step2Labels = mixedMoment B raw7610step3 raw7610step3Labels := by
      have ha : raw7610step3 = (fun i j => raw7610step2 (permutation2 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7610step3 raw7610step2; decide +kernel
      have hl : raw7610step3Labels = raw7610step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7610step2 raw7610step2Labels permutation2 permutation3
    mixedMoment B raw7610step3 raw7610step3Labels = mixedMoment B raw7610step4 raw7610step4Labels := by
      have ha : raw7610step4 = raw7610step3 := by apply Matrix.ext; unfold raw7610step4 raw7610step3; decide +kernel
      have hl : raw7610step3Labels = labelEmbedding6 ∘ raw7610step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7610step3 raw7610step3Labels raw7610step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4507 node4507Labels := by rfl

def raw7611 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw7611Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7611step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw7611step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7611step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![3, -1, -2]]
def raw7611step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7611step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw7611step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7611step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw7611step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7611 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7611 raw7611Labels = mixedMoment B node5109 node5109Labels := by
  calc
    mixedMoment B raw7611 raw7611Labels = mixedMoment B raw7611step0 raw7611step0Labels := by
      have hz : ∀ j, raw7611 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7611step0 = (fun i j => raw7611 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7611step0 raw7611; decide +kernel
      have hl : raw7611step0Labels = raw7611Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7611 raw7611Labels permutation434 hz
    mixedMoment B raw7611step0 raw7611step0Labels = mixedMoment B raw7611step1 raw7611step1Labels := by
      have hz : ∀ j, raw7611step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7611step1 = (fun i j => raw7611step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7611step1 raw7611step0; decide +kernel
      have hl : raw7611step1Labels = raw7611step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7611step0 raw7611step0Labels permutation80 hz
    mixedMoment B raw7611step1 raw7611step1Labels = mixedMoment B raw7611step2 raw7611step2Labels := by
      have ha : raw7611step2 = (fun i j => raw7611step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7611step2 raw7611step1; decide +kernel
      have hl : raw7611step2Labels = raw7611step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7611step1 raw7611step1Labels permutation8 permutation3
    mixedMoment B raw7611step2 raw7611step2Labels = mixedMoment B raw7611step3 raw7611step3Labels := by
      have ha : raw7611step3 = raw7611step2 := by apply Matrix.ext; unfold raw7611step3 raw7611step2; decide +kernel
      have hl : raw7611step2Labels = labelEmbedding6 ∘ raw7611step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7611step2 raw7611step2Labels raw7611step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5109 node5109Labels := by rfl

def raw7612 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw7612Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7612step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![3, -1, -2]]
def raw7612step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7612step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![3, -1, -2]]
def raw7612step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7612step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw7612step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7612step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw7612step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7612 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7612 raw7612Labels = mixedMoment B node5109 node5109Labels := by
  calc
    mixedMoment B raw7612 raw7612Labels = mixedMoment B raw7612step0 raw7612step0Labels := by
      have hz : ∀ j, raw7612 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7612step0 = (fun i j => raw7612 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7612step0 raw7612; decide +kernel
      have hl : raw7612step0Labels = raw7612Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7612 raw7612Labels permutation434 hz
    mixedMoment B raw7612step0 raw7612step0Labels = mixedMoment B raw7612step1 raw7612step1Labels := by
      have hz : ∀ j, raw7612step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7612step1 = (fun i j => raw7612step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7612step1 raw7612step0; decide +kernel
      have hl : raw7612step1Labels = raw7612step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7612step0 raw7612step0Labels permutation56 hz
    mixedMoment B raw7612step1 raw7612step1Labels = mixedMoment B raw7612step2 raw7612step2Labels := by
      have ha : raw7612step2 = (fun i j => raw7612step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7612step2 raw7612step1; decide +kernel
      have hl : raw7612step2Labels = raw7612step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7612step1 raw7612step1Labels permutation8 permutation3
    mixedMoment B raw7612step2 raw7612step2Labels = mixedMoment B raw7612step3 raw7612step3Labels := by
      have ha : raw7612step3 = raw7612step2 := by apply Matrix.ext; unfold raw7612step3 raw7612step2; decide +kernel
      have hl : raw7612step2Labels = labelEmbedding6 ∘ raw7612step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7612step2 raw7612step2Labels raw7612step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5109 node5109Labels := by rfl

def raw7613 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![3, -1, -2]]
def raw7613Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7613step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![3, -1, -2]]
def raw7613step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7613step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![3, -1, -2]]
def raw7613step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7613step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw7613step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7613step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw7613step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7613 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7613 raw7613Labels = mixedMoment B node5109 node5109Labels := by
  calc
    mixedMoment B raw7613 raw7613Labels = mixedMoment B raw7613step0 raw7613step0Labels := by
      have hz : ∀ j, raw7613 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7613step0 = (fun i j => raw7613 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7613step0 raw7613; decide +kernel
      have hl : raw7613step0Labels = raw7613Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7613 raw7613Labels permutation346 hz
    mixedMoment B raw7613step0 raw7613step0Labels = mixedMoment B raw7613step1 raw7613step1Labels := by
      have hz : ∀ j, raw7613step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7613step1 = (fun i j => raw7613step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7613step1 raw7613step0; decide +kernel
      have hl : raw7613step1Labels = raw7613step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7613step0 raw7613step0Labels permutation56 hz
    mixedMoment B raw7613step1 raw7613step1Labels = mixedMoment B raw7613step2 raw7613step2Labels := by
      have ha : raw7613step2 = (fun i j => raw7613step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7613step2 raw7613step1; decide +kernel
      have hl : raw7613step2Labels = raw7613step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7613step1 raw7613step1Labels permutation8 permutation3
    mixedMoment B raw7613step2 raw7613step2Labels = mixedMoment B raw7613step3 raw7613step3Labels := by
      have ha : raw7613step3 = raw7613step2 := by apply Matrix.ext; unfold raw7613step3 raw7613step2; decide +kernel
      have hl : raw7613step2Labels = labelEmbedding6 ∘ raw7613step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7613step2 raw7613step2Labels raw7613step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5109 node5109Labels := by rfl

def raw7614 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw7614Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7614step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw7614step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7614step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw7614step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7614step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0]]
def raw7614step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7614 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7614 raw7614Labels = mixedMoment B node3987 node3987Labels := by
  calc
    mixedMoment B raw7614 raw7614Labels = mixedMoment B raw7614step0 raw7614step0Labels := by
      have hz : ∀ j, raw7614 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7614step0 = (fun i j => raw7614 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7614step0 raw7614; decide +kernel
      have hl : raw7614step0Labels = raw7614Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7614 raw7614Labels permutation434 hz
    mixedMoment B raw7614step0 raw7614step0Labels = mixedMoment B raw7614step1 raw7614step1Labels := by
      have hz : ∀ j, raw7614step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7614step1 = (fun i j => raw7614step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7614step1 raw7614step0; decide +kernel
      have hl : raw7614step1Labels = raw7614step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7614step0 raw7614step0Labels permutation80 hz
    mixedMoment B raw7614step1 raw7614step1Labels = mixedMoment B raw7614step2 raw7614step2Labels := by
      have ha : raw7614step2 = (fun i j => raw7614step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7614step2 raw7614step1; decide +kernel
      have hl : raw7614step2Labels = raw7614step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7614step1 raw7614step1Labels permutation8 permutation3
    _ = mixedMoment B node3987 node3987Labels := by rfl

def raw7615 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw7615Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7615step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw7615step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7615step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw7615step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7615step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0]]
def raw7615step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7615 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7615 raw7615Labels = mixedMoment B node3987 node3987Labels := by
  calc
    mixedMoment B raw7615 raw7615Labels = mixedMoment B raw7615step0 raw7615step0Labels := by
      have hz : ∀ j, raw7615 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7615step0 = (fun i j => raw7615 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7615step0 raw7615; decide +kernel
      have hl : raw7615step0Labels = raw7615Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7615 raw7615Labels permutation434 hz
    mixedMoment B raw7615step0 raw7615step0Labels = mixedMoment B raw7615step1 raw7615step1Labels := by
      have hz : ∀ j, raw7615step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7615step1 = (fun i j => raw7615step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7615step1 raw7615step0; decide +kernel
      have hl : raw7615step1Labels = raw7615step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7615step0 raw7615step0Labels permutation56 hz
    mixedMoment B raw7615step1 raw7615step1Labels = mixedMoment B raw7615step2 raw7615step2Labels := by
      have ha : raw7615step2 = (fun i j => raw7615step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7615step2 raw7615step1; decide +kernel
      have hl : raw7615step2Labels = raw7615step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7615step1 raw7615step1Labels permutation8 permutation3
    _ = mixedMoment B node3987 node3987Labels := by rfl

def raw7616 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw7616Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7616step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw7616step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7616step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw7616step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7616step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0]]
def raw7616step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7616 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7616 raw7616Labels = mixedMoment B node3987 node3987Labels := by
  calc
    mixedMoment B raw7616 raw7616Labels = mixedMoment B raw7616step0 raw7616step0Labels := by
      have hz : ∀ j, raw7616 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7616step0 = (fun i j => raw7616 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7616step0 raw7616; decide +kernel
      have hl : raw7616step0Labels = raw7616Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7616 raw7616Labels permutation346 hz
    mixedMoment B raw7616step0 raw7616step0Labels = mixedMoment B raw7616step1 raw7616step1Labels := by
      have hz : ∀ j, raw7616step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7616step1 = (fun i j => raw7616step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7616step1 raw7616step0; decide +kernel
      have hl : raw7616step1Labels = raw7616step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7616step0 raw7616step0Labels permutation56 hz
    mixedMoment B raw7616step1 raw7616step1Labels = mixedMoment B raw7616step2 raw7616step2Labels := by
      have ha : raw7616step2 = (fun i j => raw7616step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7616step2 raw7616step1; decide +kernel
      have hl : raw7616step2Labels = raw7616step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7616step1 raw7616step1Labels permutation8 permutation3
    _ = mixedMoment B node3987 node3987Labels := by rfl

def raw7617 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw7617Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7617step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw7617step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7617step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw7617step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7617step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![2, 0, -2]]
def raw7617step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7617step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![2, -2, 0]]
def raw7617step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7617 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7617 raw7617Labels = mixedMoment B node4019 node4019Labels := by
  calc
    mixedMoment B raw7617 raw7617Labels = mixedMoment B raw7617step0 raw7617step0Labels := by
      have hz : ∀ j, raw7617 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7617step0 = (fun i j => raw7617 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7617step0 raw7617; decide +kernel
      have hl : raw7617step0Labels = raw7617Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7617 raw7617Labels permutation434 hz
    mixedMoment B raw7617step0 raw7617step0Labels = mixedMoment B raw7617step1 raw7617step1Labels := by
      have hz : ∀ j, raw7617step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7617step1 = (fun i j => raw7617step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7617step1 raw7617step0; decide +kernel
      have hl : raw7617step1Labels = raw7617step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7617step0 raw7617step0Labels permutation80 hz
    mixedMoment B raw7617step1 raw7617step1Labels = mixedMoment B raw7617step2 raw7617step2Labels := by
      have hz : ∀ j, raw7617step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw7617step2 = (fun i j => raw7617step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw7617step2 raw7617step1; decide +kernel
      have hl : raw7617step2Labels = raw7617step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7617step1 raw7617step1Labels permutation14 hz
    mixedMoment B raw7617step2 raw7617step2Labels = mixedMoment B raw7617step3 raw7617step3Labels := by
      have ha : raw7617step3 = (fun i j => raw7617step2 (permutation2 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7617step3 raw7617step2; decide +kernel
      have hl : raw7617step3Labels = raw7617step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7617step2 raw7617step2Labels permutation2 permutation3
    _ = mixedMoment B node4019 node4019Labels := by rfl

def raw7618 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2]]
def raw7618Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7618step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2]]
def raw7618step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7618step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2]]
def raw7618step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7618step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![1, 1, -2]]
def raw7618step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7618step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![1, 1, -2]]
def raw7618step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7618 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7618 raw7618Labels = mixedMoment B node4020 node4020Labels := by
  calc
    mixedMoment B raw7618 raw7618Labels = mixedMoment B raw7618step0 raw7618step0Labels := by
      have hz : ∀ j, raw7618 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7618step0 = (fun i j => raw7618 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7618step0 raw7618; decide +kernel
      have hl : raw7618step0Labels = raw7618Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7618 raw7618Labels permutation434 hz
    mixedMoment B raw7618step0 raw7618step0Labels = mixedMoment B raw7618step1 raw7618step1Labels := by
      have hz : ∀ j, raw7618step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7618step1 = (fun i j => raw7618step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7618step1 raw7618step0; decide +kernel
      have hl : raw7618step1Labels = raw7618step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7618step0 raw7618step0Labels permutation80 hz
    mixedMoment B raw7618step1 raw7618step1Labels = mixedMoment B raw7618step2 raw7618step2Labels := by
      have hz : ∀ j, raw7618step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw7618step2 = (fun i j => raw7618step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw7618step2 raw7618step1; decide +kernel
      have hl : raw7618step2Labels = raw7618step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7618step1 raw7618step1Labels permutation14 hz
    mixedMoment B raw7618step2 raw7618step2Labels = mixedMoment B raw7618step3 raw7618step3Labels := by
      have ha : raw7618step3 = (fun i j => raw7618step2 (permutation3 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7618step3 raw7618step2; decide +kernel
      have hl : raw7618step3Labels = raw7618step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7618step2 raw7618step2Labels permutation3 permutation3
    _ = mixedMoment B node4020 node4020Labels := by rfl

def raw7619 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw7619Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7619step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw7619step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7619step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw7619step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7619step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw7619step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7619 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7619 raw7619Labels = mixedMoment B node1087 node1087Labels := by
  calc
    mixedMoment B raw7619 raw7619Labels = mixedMoment B raw7619step0 raw7619step0Labels := by
      have hz : ∀ j, raw7619 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7619step0 = (fun i j => raw7619 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7619step0 raw7619; decide +kernel
      have hl : raw7619step0Labels = raw7619Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7619 raw7619Labels permutation434 hz
    mixedMoment B raw7619step0 raw7619step0Labels = mixedMoment B raw7619step1 raw7619step1Labels := by
      have hz : ∀ j, raw7619step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7619step1 = (fun i j => raw7619step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7619step1 raw7619step0; decide +kernel
      have hl : raw7619step1Labels = raw7619step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7619step0 raw7619step0Labels permutation80 hz
    mixedMoment B raw7619step1 raw7619step1Labels = mixedMoment B raw7619step2 raw7619step2Labels := by
      have ha : raw7619step2 = (fun i j => raw7619step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7619step2 raw7619step1; decide +kernel
      have hl : raw7619step2Labels = raw7619step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7619step1 raw7619step1Labels permutation8 permutation3
    _ = mixedMoment B node1087 node1087Labels := by rfl

def raw7620 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw7620Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7620step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw7620step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7620step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw7620step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7620 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7620 raw7620Labels = mixedMoment B node2515 node2515Labels := by
  calc
    mixedMoment B raw7620 raw7620Labels = mixedMoment B raw7620step0 raw7620step0Labels := by
      have hz : ∀ j, raw7620 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7620step0 = (fun i j => raw7620 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7620step0 raw7620; decide +kernel
      have hl : raw7620step0Labels = raw7620Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7620 raw7620Labels permutation434 hz
    mixedMoment B raw7620step0 raw7620step0Labels = mixedMoment B raw7620step1 raw7620step1Labels := by
      have ha : raw7620step1 = (fun i j => raw7620step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7620step1 raw7620step0; decide +kernel
      have hl : raw7620step1Labels = raw7620step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7620step0 raw7620step0Labels permutation38 permutation3
    _ = mixedMoment B node2515 node2515Labels := by rfl

def raw7621 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw7621Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7621step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw7621step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7621step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw7621step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7621 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7621 raw7621Labels = mixedMoment B node2515 node2515Labels := by
  calc
    mixedMoment B raw7621 raw7621Labels = mixedMoment B raw7621step0 raw7621step0Labels := by
      have hz : ∀ j, raw7621 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7621step0 = (fun i j => raw7621 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7621step0 raw7621; decide +kernel
      have hl : raw7621step0Labels = raw7621Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7621 raw7621Labels permutation346 hz
    mixedMoment B raw7621step0 raw7621step0Labels = mixedMoment B raw7621step1 raw7621step1Labels := by
      have ha : raw7621step1 = (fun i j => raw7621step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7621step1 raw7621step0; decide +kernel
      have hl : raw7621step1Labels = raw7621step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7621step0 raw7621step0Labels permutation38 permutation3
    _ = mixedMoment B node2515 node2515Labels := by rfl

def raw7622 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw7622Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7622step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw7622step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7622step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw7622step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7622step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7622step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7622 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7622 raw7622Labels = mixedMoment B node2768 node2768Labels := by
  calc
    mixedMoment B raw7622 raw7622Labels = mixedMoment B raw7622step0 raw7622step0Labels := by
      have hz : ∀ j, raw7622 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7622step0 = (fun i j => raw7622 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7622step0 raw7622; decide +kernel
      have hl : raw7622step0Labels = raw7622Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7622 raw7622Labels permutation434 hz
    mixedMoment B raw7622step0 raw7622step0Labels = mixedMoment B raw7622step1 raw7622step1Labels := by
      have hz : ∀ j, raw7622step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7622step1 = (fun i j => raw7622step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7622step1 raw7622step0; decide +kernel
      have hl : raw7622step1Labels = raw7622step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7622step0 raw7622step0Labels permutation80 hz
    mixedMoment B raw7622step1 raw7622step1Labels = mixedMoment B raw7622step2 raw7622step2Labels := by
      have ha : raw7622step2 = (fun i j => raw7622step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7622step2 raw7622step1; decide +kernel
      have hl : raw7622step2Labels = raw7622step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7622step1 raw7622step1Labels permutation10 permutation3
    _ = mixedMoment B node2768 node2768Labels := by rfl

def raw7623 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2]]
def raw7623Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7623step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2]]
def raw7623step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7623step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![1, -2, 1], ![1, 1, -2]]
def raw7623step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7623step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw7623step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7623 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7623 raw7623Labels = mixedMoment B node2782 node2782Labels := by
  calc
    mixedMoment B raw7623 raw7623Labels = mixedMoment B raw7623step0 raw7623step0Labels := by
      have hz : ∀ j, raw7623 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7623step0 = (fun i j => raw7623 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7623step0 raw7623; decide +kernel
      have hl : raw7623step0Labels = raw7623Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7623 raw7623Labels permutation434 hz
    mixedMoment B raw7623step0 raw7623step0Labels = mixedMoment B raw7623step1 raw7623step1Labels := by
      have hz : ∀ j, raw7623step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7623step1 = (fun i j => raw7623step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7623step1 raw7623step0; decide +kernel
      have hl : raw7623step1Labels = raw7623step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7623step0 raw7623step0Labels permutation80 hz
    mixedMoment B raw7623step1 raw7623step1Labels = mixedMoment B raw7623step2 raw7623step2Labels := by
      have ha : raw7623step2 = (fun i j => raw7623step1 (permutation12 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7623step2 raw7623step1; decide +kernel
      have hl : raw7623step2Labels = raw7623step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7623step1 raw7623step1Labels permutation12 permutation3
    _ = mixedMoment B node2782 node2782Labels := by rfl

def raw7624 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw7624Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7624step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw7624step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7624step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw7624step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7624step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw7624step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7624 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7624 raw7624Labels = mixedMoment B node1087 node1087Labels := by
  calc
    mixedMoment B raw7624 raw7624Labels = mixedMoment B raw7624step0 raw7624step0Labels := by
      have hz : ∀ j, raw7624 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7624step0 = (fun i j => raw7624 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7624step0 raw7624; decide +kernel
      have hl : raw7624step0Labels = raw7624Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7624 raw7624Labels permutation434 hz
    mixedMoment B raw7624step0 raw7624step0Labels = mixedMoment B raw7624step1 raw7624step1Labels := by
      have hz : ∀ j, raw7624step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7624step1 = (fun i j => raw7624step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7624step1 raw7624step0; decide +kernel
      have hl : raw7624step1Labels = raw7624step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7624step0 raw7624step0Labels permutation56 hz
    mixedMoment B raw7624step1 raw7624step1Labels = mixedMoment B raw7624step2 raw7624step2Labels := by
      have ha : raw7624step2 = (fun i j => raw7624step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7624step2 raw7624step1; decide +kernel
      have hl : raw7624step2Labels = raw7624step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7624step1 raw7624step1Labels permutation8 permutation3
    _ = mixedMoment B node1087 node1087Labels := by rfl

def raw7625 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw7625Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7625step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw7625step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7625step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw7625step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7625 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7625 raw7625Labels = mixedMoment B node2515 node2515Labels := by
  calc
    mixedMoment B raw7625 raw7625Labels = mixedMoment B raw7625step0 raw7625step0Labels := by
      have hz : ∀ j, raw7625 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7625step0 = (fun i j => raw7625 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7625step0 raw7625; decide +kernel
      have hl : raw7625step0Labels = raw7625Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7625 raw7625Labels permutation434 hz
    mixedMoment B raw7625step0 raw7625step0Labels = mixedMoment B raw7625step1 raw7625step1Labels := by
      have ha : raw7625step1 = (fun i j => raw7625step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7625step1 raw7625step0; decide +kernel
      have hl : raw7625step1Labels = raw7625step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7625step0 raw7625step0Labels permutation32 permutation3
    _ = mixedMoment B node2515 node2515Labels := by rfl

def raw7626 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw7626Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7626step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw7626step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7626step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw7626step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7626 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7626 raw7626Labels = mixedMoment B node2515 node2515Labels := by
  calc
    mixedMoment B raw7626 raw7626Labels = mixedMoment B raw7626step0 raw7626step0Labels := by
      have hz : ∀ j, raw7626 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw7626step0 = (fun i j => raw7626 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw7626step0 raw7626; decide +kernel
      have hl : raw7626step0Labels = raw7626Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7626 raw7626Labels permutation265 hz
    mixedMoment B raw7626step0 raw7626step0Labels = mixedMoment B raw7626step1 raw7626step1Labels := by
      have ha : raw7626step1 = (fun i j => raw7626step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7626step1 raw7626step0; decide +kernel
      have hl : raw7626step1Labels = raw7626step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7626step0 raw7626step0Labels permutation38 permutation3
    _ = mixedMoment B node2515 node2515Labels := by rfl

def raw7627 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw7627Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7627step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw7627step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7627step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw7627step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7627step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7627step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7627 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7627 raw7627Labels = mixedMoment B node2768 node2768Labels := by
  calc
    mixedMoment B raw7627 raw7627Labels = mixedMoment B raw7627step0 raw7627step0Labels := by
      have hz : ∀ j, raw7627 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7627step0 = (fun i j => raw7627 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7627step0 raw7627; decide +kernel
      have hl : raw7627step0Labels = raw7627Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7627 raw7627Labels permutation434 hz
    mixedMoment B raw7627step0 raw7627step0Labels = mixedMoment B raw7627step1 raw7627step1Labels := by
      have hz : ∀ j, raw7627step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7627step1 = (fun i j => raw7627step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7627step1 raw7627step0; decide +kernel
      have hl : raw7627step1Labels = raw7627step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7627step0 raw7627step0Labels permutation56 hz
    mixedMoment B raw7627step1 raw7627step1Labels = mixedMoment B raw7627step2 raw7627step2Labels := by
      have ha : raw7627step2 = (fun i j => raw7627step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7627step2 raw7627step1; decide +kernel
      have hl : raw7627step2Labels = raw7627step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7627step1 raw7627step1Labels permutation10 permutation3
    _ = mixedMoment B node2768 node2768Labels := by rfl

def raw7628 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2]]
def raw7628Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7628step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![1, 1, -2]]
def raw7628step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7628step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![1, -2, 1], ![1, 1, -2]]
def raw7628step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7628step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw7628step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7628 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7628 raw7628Labels = mixedMoment B node2782 node2782Labels := by
  calc
    mixedMoment B raw7628 raw7628Labels = mixedMoment B raw7628step0 raw7628step0Labels := by
      have hz : ∀ j, raw7628 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7628step0 = (fun i j => raw7628 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7628step0 raw7628; decide +kernel
      have hl : raw7628step0Labels = raw7628Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7628 raw7628Labels permutation434 hz
    mixedMoment B raw7628step0 raw7628step0Labels = mixedMoment B raw7628step1 raw7628step1Labels := by
      have hz : ∀ j, raw7628step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7628step1 = (fun i j => raw7628step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7628step1 raw7628step0; decide +kernel
      have hl : raw7628step1Labels = raw7628step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7628step0 raw7628step0Labels permutation56 hz
    mixedMoment B raw7628step1 raw7628step1Labels = mixedMoment B raw7628step2 raw7628step2Labels := by
      have ha : raw7628step2 = (fun i j => raw7628step1 (permutation12 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7628step2 raw7628step1; decide +kernel
      have hl : raw7628step2Labels = raw7628step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7628step1 raw7628step1Labels permutation12 permutation3
    _ = mixedMoment B node2782 node2782Labels := by rfl

def raw7629 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw7629Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7629step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw7629step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7629step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw7629step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7629step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw7629step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7629 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7629 raw7629Labels = mixedMoment B node1087 node1087Labels := by
  calc
    mixedMoment B raw7629 raw7629Labels = mixedMoment B raw7629step0 raw7629step0Labels := by
      have hz : ∀ j, raw7629 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7629step0 = (fun i j => raw7629 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7629step0 raw7629; decide +kernel
      have hl : raw7629step0Labels = raw7629Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7629 raw7629Labels permutation346 hz
    mixedMoment B raw7629step0 raw7629step0Labels = mixedMoment B raw7629step1 raw7629step1Labels := by
      have hz : ∀ j, raw7629step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7629step1 = (fun i j => raw7629step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7629step1 raw7629step0; decide +kernel
      have hl : raw7629step1Labels = raw7629step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7629step0 raw7629step0Labels permutation56 hz
    mixedMoment B raw7629step1 raw7629step1Labels = mixedMoment B raw7629step2 raw7629step2Labels := by
      have ha : raw7629step2 = (fun i j => raw7629step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7629step2 raw7629step1; decide +kernel
      have hl : raw7629step2Labels = raw7629step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7629step1 raw7629step1Labels permutation8 permutation3
    _ = mixedMoment B node1087 node1087Labels := by rfl

def raw7630 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw7630Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7630step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw7630step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7630step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw7630step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7630 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7630 raw7630Labels = mixedMoment B node2515 node2515Labels := by
  calc
    mixedMoment B raw7630 raw7630Labels = mixedMoment B raw7630step0 raw7630step0Labels := by
      have hz : ∀ j, raw7630 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7630step0 = (fun i j => raw7630 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7630step0 raw7630; decide +kernel
      have hl : raw7630step0Labels = raw7630Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7630 raw7630Labels permutation346 hz
    mixedMoment B raw7630step0 raw7630step0Labels = mixedMoment B raw7630step1 raw7630step1Labels := by
      have ha : raw7630step1 = (fun i j => raw7630step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7630step1 raw7630step0; decide +kernel
      have hl : raw7630step1Labels = raw7630step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7630step0 raw7630step0Labels permutation32 permutation3
    _ = mixedMoment B node2515 node2515Labels := by rfl

def raw7631 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw7631Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7631step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw7631step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7631step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw7631step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7631 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7631 raw7631Labels = mixedMoment B node2515 node2515Labels := by
  calc
    mixedMoment B raw7631 raw7631Labels = mixedMoment B raw7631step0 raw7631step0Labels := by
      have hz : ∀ j, raw7631 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw7631step0 = (fun i j => raw7631 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw7631step0 raw7631; decide +kernel
      have hl : raw7631step0Labels = raw7631Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7631 raw7631Labels permutation265 hz
    mixedMoment B raw7631step0 raw7631step0Labels = mixedMoment B raw7631step1 raw7631step1Labels := by
      have ha : raw7631step1 = (fun i j => raw7631step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7631step1 raw7631step0; decide +kernel
      have hl : raw7631step1Labels = raw7631step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7631step0 raw7631step0Labels permutation32 permutation3
    _ = mixedMoment B node2515 node2515Labels := by rfl

def raw7632 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw7632Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7632step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw7632step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7632step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw7632step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7632step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7632step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7632 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7632 raw7632Labels = mixedMoment B node2768 node2768Labels := by
  calc
    mixedMoment B raw7632 raw7632Labels = mixedMoment B raw7632step0 raw7632step0Labels := by
      have hz : ∀ j, raw7632 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7632step0 = (fun i j => raw7632 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7632step0 raw7632; decide +kernel
      have hl : raw7632step0Labels = raw7632Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7632 raw7632Labels permutation346 hz
    mixedMoment B raw7632step0 raw7632step0Labels = mixedMoment B raw7632step1 raw7632step1Labels := by
      have hz : ∀ j, raw7632step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7632step1 = (fun i j => raw7632step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7632step1 raw7632step0; decide +kernel
      have hl : raw7632step1Labels = raw7632step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7632step0 raw7632step0Labels permutation56 hz
    mixedMoment B raw7632step1 raw7632step1Labels = mixedMoment B raw7632step2 raw7632step2Labels := by
      have ha : raw7632step2 = (fun i j => raw7632step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7632step2 raw7632step1; decide +kernel
      have hl : raw7632step2Labels = raw7632step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7632step1 raw7632step1Labels permutation10 permutation3
    _ = mixedMoment B node2768 node2768Labels := by rfl

def raw7633 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![1, 1, -2]]
def raw7633Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7633step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![1, 1, -2]]
def raw7633step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7633step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![1, -2, 1], ![1, 1, -2]]
def raw7633step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7633step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw7633step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7633 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7633 raw7633Labels = mixedMoment B node2782 node2782Labels := by
  calc
    mixedMoment B raw7633 raw7633Labels = mixedMoment B raw7633step0 raw7633step0Labels := by
      have hz : ∀ j, raw7633 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7633step0 = (fun i j => raw7633 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7633step0 raw7633; decide +kernel
      have hl : raw7633step0Labels = raw7633Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7633 raw7633Labels permutation346 hz
    mixedMoment B raw7633step0 raw7633step0Labels = mixedMoment B raw7633step1 raw7633step1Labels := by
      have hz : ∀ j, raw7633step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7633step1 = (fun i j => raw7633step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7633step1 raw7633step0; decide +kernel
      have hl : raw7633step1Labels = raw7633step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7633step0 raw7633step0Labels permutation56 hz
    mixedMoment B raw7633step1 raw7633step1Labels = mixedMoment B raw7633step2 raw7633step2Labels := by
      have ha : raw7633step2 = (fun i j => raw7633step1 (permutation12 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7633step2 raw7633step1; decide +kernel
      have hl : raw7633step2Labels = raw7633step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7633step1 raw7633step1Labels permutation12 permutation3
    _ = mixedMoment B node2782 node2782Labels := by rfl

def raw7634 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![2, 0, -2]]
def raw7634Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7634step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![2, 0, -2]]
def raw7634step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7634step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![2, -3, 1], ![2, 0, -2]]
def raw7634step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7634step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 3, 1], ![2, -3, 1], ![2, 0, -2]]
def raw7634step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7634step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -2, 0], ![2, 1, -3]]
def raw7634step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7634 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7634 raw7634Labels = mixedMoment B node1094 node1094Labels := by
  calc
    mixedMoment B raw7634 raw7634Labels = mixedMoment B raw7634step0 raw7634step0Labels := by
      have hz : ∀ j, raw7634 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7634step0 = (fun i j => raw7634 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7634step0 raw7634; decide +kernel
      have hl : raw7634step0Labels = raw7634Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7634 raw7634Labels permutation434 hz
    mixedMoment B raw7634step0 raw7634step0Labels = mixedMoment B raw7634step1 raw7634step1Labels := by
      have hz : ∀ j, raw7634step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7634step1 = (fun i j => raw7634step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7634step1 raw7634step0; decide +kernel
      have hl : raw7634step1Labels = raw7634step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7634step0 raw7634step0Labels permutation80 hz
    mixedMoment B raw7634step1 raw7634step1Labels = mixedMoment B raw7634step2 raw7634step2Labels := by
      have hz : ∀ j, raw7634step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw7634step2 = (fun i j => raw7634step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw7634step2 raw7634step1; decide +kernel
      have hl : raw7634step2Labels = raw7634step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7634step1 raw7634step1Labels permutation14 hz
    mixedMoment B raw7634step2 raw7634step2Labels = mixedMoment B raw7634step3 raw7634step3Labels := by
      have ha : raw7634step3 = (fun i j => raw7634step2 (permutation3 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7634step3 raw7634step2; decide +kernel
      have hl : raw7634step3Labels = raw7634step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7634step2 raw7634step2Labels permutation3 permutation3
    _ = mixedMoment B node1094 node1094Labels := by rfl

def raw7635 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![2, 0, -2]]
def raw7635Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7635step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![2, 0, -2]]
def raw7635step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7635step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![2, -3, 1], ![2, 0, -2]]
def raw7635step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7635step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw7635step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7635 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7635 raw7635Labels = mixedMoment B node2522 node2522Labels := by
  calc
    mixedMoment B raw7635 raw7635Labels = mixedMoment B raw7635step0 raw7635step0Labels := by
      have hz : ∀ j, raw7635 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7635step0 = (fun i j => raw7635 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7635step0 raw7635; decide +kernel
      have hl : raw7635step0Labels = raw7635Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7635 raw7635Labels permutation434 hz
    mixedMoment B raw7635step0 raw7635step0Labels = mixedMoment B raw7635step1 raw7635step1Labels := by
      have hz : ∀ j, raw7635step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7635step1 = (fun i j => raw7635step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7635step1 raw7635step0; decide +kernel
      have hl : raw7635step1Labels = raw7635step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7635step0 raw7635step0Labels permutation80 hz
    mixedMoment B raw7635step1 raw7635step1Labels = mixedMoment B raw7635step2 raw7635step2Labels := by
      have ha : raw7635step2 = (fun i j => raw7635step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7635step2 raw7635step1; decide +kernel
      have hl : raw7635step2Labels = raw7635step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7635step1 raw7635step1Labels permutation9 permutation3
    _ = mixedMoment B node2522 node2522Labels := by rfl

def raw7636 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![2, 0, -2]]
def raw7636Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7636step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![2, 0, -2]]
def raw7636step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7636step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![2, -3, 1], ![2, 0, -2]]
def raw7636step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7636step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw7636step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7636 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7636 raw7636Labels = mixedMoment B node2522 node2522Labels := by
  calc
    mixedMoment B raw7636 raw7636Labels = mixedMoment B raw7636step0 raw7636step0Labels := by
      have hz : ∀ j, raw7636 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7636step0 = (fun i j => raw7636 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7636step0 raw7636; decide +kernel
      have hl : raw7636step0Labels = raw7636Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7636 raw7636Labels permutation434 hz
    mixedMoment B raw7636step0 raw7636step0Labels = mixedMoment B raw7636step1 raw7636step1Labels := by
      have hz : ∀ j, raw7636step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7636step1 = (fun i j => raw7636step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7636step1 raw7636step0; decide +kernel
      have hl : raw7636step1Labels = raw7636step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7636step0 raw7636step0Labels permutation56 hz
    mixedMoment B raw7636step1 raw7636step1Labels = mixedMoment B raw7636step2 raw7636step2Labels := by
      have ha : raw7636step2 = (fun i j => raw7636step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7636step2 raw7636step1; decide +kernel
      have hl : raw7636step2Labels = raw7636step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7636step1 raw7636step1Labels permutation9 permutation3
    _ = mixedMoment B node2522 node2522Labels := by rfl

def raw7637 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![2, 0, -2]]
def raw7637Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7637step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![2, 0, -2]]
def raw7637step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7637step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![2, -3, 1], ![2, 0, -2]]
def raw7637step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7637step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw7637step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7637 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7637 raw7637Labels = mixedMoment B node2522 node2522Labels := by
  calc
    mixedMoment B raw7637 raw7637Labels = mixedMoment B raw7637step0 raw7637step0Labels := by
      have hz : ∀ j, raw7637 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7637step0 = (fun i j => raw7637 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7637step0 raw7637; decide +kernel
      have hl : raw7637step0Labels = raw7637Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7637 raw7637Labels permutation346 hz
    mixedMoment B raw7637step0 raw7637step0Labels = mixedMoment B raw7637step1 raw7637step1Labels := by
      have hz : ∀ j, raw7637step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7637step1 = (fun i j => raw7637step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7637step1 raw7637step0; decide +kernel
      have hl : raw7637step1Labels = raw7637step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7637step0 raw7637step0Labels permutation56 hz
    mixedMoment B raw7637step1 raw7637step1Labels = mixedMoment B raw7637step2 raw7637step2Labels := by
      have ha : raw7637step2 = (fun i j => raw7637step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7637step2 raw7637step1; decide +kernel
      have hl : raw7637step2Labels = raw7637step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7637step1 raw7637step1Labels permutation9 permutation3
    _ = mixedMoment B node2522 node2522Labels := by rfl

def raw7638 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![1, 1, -2]]
def raw7638Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7638step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![1, 1, -2]]
def raw7638step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7638step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![2, -3, 1], ![1, 1, -2]]
def raw7638step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7638step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![2, -3, 1], ![1, 1, -2]]
def raw7638step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7638step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![2, 1, -3]]
def raw7638step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7638 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7638 raw7638Labels = mixedMoment B node2783 node2783Labels := by
  calc
    mixedMoment B raw7638 raw7638Labels = mixedMoment B raw7638step0 raw7638step0Labels := by
      have hz : ∀ j, raw7638 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7638step0 = (fun i j => raw7638 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7638step0 raw7638; decide +kernel
      have hl : raw7638step0Labels = raw7638Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7638 raw7638Labels permutation434 hz
    mixedMoment B raw7638step0 raw7638step0Labels = mixedMoment B raw7638step1 raw7638step1Labels := by
      have hz : ∀ j, raw7638step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7638step1 = (fun i j => raw7638step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7638step1 raw7638step0; decide +kernel
      have hl : raw7638step1Labels = raw7638step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7638step0 raw7638step0Labels permutation80 hz
    mixedMoment B raw7638step1 raw7638step1Labels = mixedMoment B raw7638step2 raw7638step2Labels := by
      have hz : ∀ j, raw7638step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw7638step2 = (fun i j => raw7638step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw7638step2 raw7638step1; decide +kernel
      have hl : raw7638step2Labels = raw7638step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7638step1 raw7638step1Labels permutation14 hz
    mixedMoment B raw7638step2 raw7638step2Labels = mixedMoment B raw7638step3 raw7638step3Labels := by
      have ha : raw7638step3 = (fun i j => raw7638step2 (permutation3 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7638step3 raw7638step2; decide +kernel
      have hl : raw7638step3Labels = raw7638step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7638step2 raw7638step2Labels permutation3 permutation3
    _ = mixedMoment B node2783 node2783Labels := by rfl

def raw7639 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw7639Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7639step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw7639step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7639step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw7639step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7639step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![3, -1, -2]]
def raw7639step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7639step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![3, -2, -1]]
def raw7639step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7639 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7639 raw7639Labels = mixedMoment B node1091 node1091Labels := by
  calc
    mixedMoment B raw7639 raw7639Labels = mixedMoment B raw7639step0 raw7639step0Labels := by
      have hz : ∀ j, raw7639 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7639step0 = (fun i j => raw7639 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7639step0 raw7639; decide +kernel
      have hl : raw7639step0Labels = raw7639Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7639 raw7639Labels permutation434 hz
    mixedMoment B raw7639step0 raw7639step0Labels = mixedMoment B raw7639step1 raw7639step1Labels := by
      have hz : ∀ j, raw7639step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7639step1 = (fun i j => raw7639step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7639step1 raw7639step0; decide +kernel
      have hl : raw7639step1Labels = raw7639step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7639step0 raw7639step0Labels permutation80 hz
    mixedMoment B raw7639step1 raw7639step1Labels = mixedMoment B raw7639step2 raw7639step2Labels := by
      have hz : ∀ j, raw7639step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw7639step2 = (fun i j => raw7639step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw7639step2 raw7639step1; decide +kernel
      have hl : raw7639step2Labels = raw7639step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7639step1 raw7639step1Labels permutation14 hz
    mixedMoment B raw7639step2 raw7639step2Labels = mixedMoment B raw7639step3 raw7639step3Labels := by
      have ha : raw7639step3 = (fun i j => raw7639step2 (permutation2 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7639step3 raw7639step2; decide +kernel
      have hl : raw7639step3Labels = raw7639step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7639step2 raw7639step2Labels permutation2 permutation3
    _ = mixedMoment B node1091 node1091Labels := by rfl

def raw7640 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw7640Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7640step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw7640step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7640step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![3, -1, -2]]
def raw7640step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7640step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw7640step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7640 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7640 raw7640Labels = mixedMoment B node2519 node2519Labels := by
  calc
    mixedMoment B raw7640 raw7640Labels = mixedMoment B raw7640step0 raw7640step0Labels := by
      have hz : ∀ j, raw7640 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7640step0 = (fun i j => raw7640 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7640step0 raw7640; decide +kernel
      have hl : raw7640step0Labels = raw7640Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7640 raw7640Labels permutation434 hz
    mixedMoment B raw7640step0 raw7640step0Labels = mixedMoment B raw7640step1 raw7640step1Labels := by
      have hz : ∀ j, raw7640step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7640step1 = (fun i j => raw7640step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7640step1 raw7640step0; decide +kernel
      have hl : raw7640step1Labels = raw7640step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7640step0 raw7640step0Labels permutation80 hz
    mixedMoment B raw7640step1 raw7640step1Labels = mixedMoment B raw7640step2 raw7640step2Labels := by
      have ha : raw7640step2 = (fun i j => raw7640step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7640step2 raw7640step1; decide +kernel
      have hl : raw7640step2Labels = raw7640step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7640step1 raw7640step1Labels permutation8 permutation3
    _ = mixedMoment B node2519 node2519Labels := by rfl

def raw7641 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw7641Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7641step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![3, -1, -2]]
def raw7641step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7641step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![3, -1, -2]]
def raw7641step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7641step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw7641step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7641 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7641 raw7641Labels = mixedMoment B node2519 node2519Labels := by
  calc
    mixedMoment B raw7641 raw7641Labels = mixedMoment B raw7641step0 raw7641step0Labels := by
      have hz : ∀ j, raw7641 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7641step0 = (fun i j => raw7641 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7641step0 raw7641; decide +kernel
      have hl : raw7641step0Labels = raw7641Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7641 raw7641Labels permutation434 hz
    mixedMoment B raw7641step0 raw7641step0Labels = mixedMoment B raw7641step1 raw7641step1Labels := by
      have hz : ∀ j, raw7641step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7641step1 = (fun i j => raw7641step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7641step1 raw7641step0; decide +kernel
      have hl : raw7641step1Labels = raw7641step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7641step0 raw7641step0Labels permutation56 hz
    mixedMoment B raw7641step1 raw7641step1Labels = mixedMoment B raw7641step2 raw7641step2Labels := by
      have ha : raw7641step2 = (fun i j => raw7641step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7641step2 raw7641step1; decide +kernel
      have hl : raw7641step2Labels = raw7641step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7641step1 raw7641step1Labels permutation8 permutation3
    _ = mixedMoment B node2519 node2519Labels := by rfl

def raw7642 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![3, -1, -2]]
def raw7642Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7642step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![3, -1, -2]]
def raw7642step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7642step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![3, -1, -2]]
def raw7642step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7642step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw7642step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7642 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7642 raw7642Labels = mixedMoment B node2519 node2519Labels := by
  calc
    mixedMoment B raw7642 raw7642Labels = mixedMoment B raw7642step0 raw7642step0Labels := by
      have hz : ∀ j, raw7642 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7642step0 = (fun i j => raw7642 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7642step0 raw7642; decide +kernel
      have hl : raw7642step0Labels = raw7642Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7642 raw7642Labels permutation346 hz
    mixedMoment B raw7642step0 raw7642step0Labels = mixedMoment B raw7642step1 raw7642step1Labels := by
      have hz : ∀ j, raw7642step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7642step1 = (fun i j => raw7642step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7642step1 raw7642step0; decide +kernel
      have hl : raw7642step1Labels = raw7642step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7642step0 raw7642step0Labels permutation56 hz
    mixedMoment B raw7642step1 raw7642step1Labels = mixedMoment B raw7642step2 raw7642step2Labels := by
      have ha : raw7642step2 = (fun i j => raw7642step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7642step2 raw7642step1; decide +kernel
      have hl : raw7642step2Labels = raw7642step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7642step1 raw7642step1Labels permutation8 permutation3
    _ = mixedMoment B node2519 node2519Labels := by rfl

def raw7643 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw7643Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7643step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw7643step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7643step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw7643step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7643step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![3, -1, -2]]
def raw7643step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7643step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![3, -2, -1]]
def raw7643step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7643 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7643 raw7643Labels = mixedMoment B node2770 node2770Labels := by
  calc
    mixedMoment B raw7643 raw7643Labels = mixedMoment B raw7643step0 raw7643step0Labels := by
      have hz : ∀ j, raw7643 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7643step0 = (fun i j => raw7643 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7643step0 raw7643; decide +kernel
      have hl : raw7643step0Labels = raw7643Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7643 raw7643Labels permutation434 hz
    mixedMoment B raw7643step0 raw7643step0Labels = mixedMoment B raw7643step1 raw7643step1Labels := by
      have hz : ∀ j, raw7643step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7643step1 = (fun i j => raw7643step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7643step1 raw7643step0; decide +kernel
      have hl : raw7643step1Labels = raw7643step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7643step0 raw7643step0Labels permutation80 hz
    mixedMoment B raw7643step1 raw7643step1Labels = mixedMoment B raw7643step2 raw7643step2Labels := by
      have hz : ∀ j, raw7643step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw7643step2 = (fun i j => raw7643step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw7643step2 raw7643step1; decide +kernel
      have hl : raw7643step2Labels = raw7643step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7643step1 raw7643step1Labels permutation14 hz
    mixedMoment B raw7643step2 raw7643step2Labels = mixedMoment B raw7643step3 raw7643step3Labels := by
      have ha : raw7643step3 = (fun i j => raw7643step2 (permutation2 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7643step3 raw7643step2; decide +kernel
      have hl : raw7643step3Labels = raw7643step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7643step2 raw7643step2Labels permutation2 permutation3
    _ = mixedMoment B node2770 node2770Labels := by rfl

def raw7644 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw7644Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7644step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw7644step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7644step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw7644step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7644step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw7644step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw7644step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw7644step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7644 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7644 raw7644Labels = mixedMoment B node5291 node5291Labels := by
  calc
    mixedMoment B raw7644 raw7644Labels = mixedMoment B raw7644step0 raw7644step0Labels := by
      have hz : ∀ j, raw7644 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7644step0 = (fun i j => raw7644 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7644step0 raw7644; decide +kernel
      have hl : raw7644step0Labels = raw7644Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7644 raw7644Labels permutation434 hz
    mixedMoment B raw7644step0 raw7644step0Labels = mixedMoment B raw7644step1 raw7644step1Labels := by
      have hz : ∀ j, raw7644step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7644step1 = (fun i j => raw7644step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7644step1 raw7644step0; decide +kernel
      have hl : raw7644step1Labels = raw7644step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7644step0 raw7644step0Labels permutation56 hz
    mixedMoment B raw7644step1 raw7644step1Labels = mixedMoment B raw7644step2 raw7644step2Labels := by
      have ha : raw7644step2 = (fun i j => raw7644step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw7644step2 raw7644step1; decide +kernel
      have hl : raw7644step2Labels = raw7644step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7644step1 raw7644step1Labels permutation8 permutation7
    mixedMoment B raw7644step2 raw7644step2Labels = mixedMoment B raw7644step3 raw7644step3Labels := by
      have ha : raw7644step3 = raw7644step2 := by apply Matrix.ext; unfold raw7644step3 raw7644step2; decide +kernel
      have hl : raw7644step2Labels = labelEmbedding10 ∘ raw7644step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7644step2 raw7644step2Labels raw7644step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5291 node5291Labels := by rfl

def raw7645 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw7645Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7645step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw7645step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7645step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw7645step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7645step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw7645step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw7645step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw7645step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7645 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7645 raw7645Labels = mixedMoment B node5291 node5291Labels := by
  calc
    mixedMoment B raw7645 raw7645Labels = mixedMoment B raw7645step0 raw7645step0Labels := by
      have hz : ∀ j, raw7645 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7645step0 = (fun i j => raw7645 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7645step0 raw7645; decide +kernel
      have hl : raw7645step0Labels = raw7645Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7645 raw7645Labels permutation346 hz
    mixedMoment B raw7645step0 raw7645step0Labels = mixedMoment B raw7645step1 raw7645step1Labels := by
      have hz : ∀ j, raw7645step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7645step1 = (fun i j => raw7645step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7645step1 raw7645step0; decide +kernel
      have hl : raw7645step1Labels = raw7645step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7645step0 raw7645step0Labels permutation56 hz
    mixedMoment B raw7645step1 raw7645step1Labels = mixedMoment B raw7645step2 raw7645step2Labels := by
      have ha : raw7645step2 = (fun i j => raw7645step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw7645step2 raw7645step1; decide +kernel
      have hl : raw7645step2Labels = raw7645step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7645step1 raw7645step1Labels permutation8 permutation7
    mixedMoment B raw7645step2 raw7645step2Labels = mixedMoment B raw7645step3 raw7645step3Labels := by
      have ha : raw7645step3 = raw7645step2 := by apply Matrix.ext; unfold raw7645step3 raw7645step2; decide +kernel
      have hl : raw7645step2Labels = labelEmbedding10 ∘ raw7645step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7645step2 raw7645step2Labels raw7645step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5291 node5291Labels := by rfl

def raw7646 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7646Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7646step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7646step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7646step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7646step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7646step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![-2, 0, 2]]
def raw7646step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7646step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![2, 0, -2]]
def raw7646step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw7646step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![2, 0, -2]]
def raw7646step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7646 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7646 raw7646Labels = mixedMoment B node5308 node5308Labels := by
  calc
    mixedMoment B raw7646 raw7646Labels = mixedMoment B raw7646step0 raw7646step0Labels := by
      have hz : ∀ j, raw7646 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7646step0 = (fun i j => raw7646 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7646step0 raw7646; decide +kernel
      have hl : raw7646step0Labels = raw7646Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7646 raw7646Labels permutation434 hz
    mixedMoment B raw7646step0 raw7646step0Labels = mixedMoment B raw7646step1 raw7646step1Labels := by
      have hz : ∀ j, raw7646step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7646step1 = (fun i j => raw7646step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7646step1 raw7646step0; decide +kernel
      have hl : raw7646step1Labels = raw7646step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7646step0 raw7646step0Labels permutation80 hz
    mixedMoment B raw7646step1 raw7646step1Labels = mixedMoment B raw7646step2 raw7646step2Labels := by
      have hz : ∀ j, raw7646step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw7646step2 = (fun i j => raw7646step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw7646step2 raw7646step1; decide +kernel
      have hl : raw7646step2Labels = raw7646step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7646step1 raw7646step1Labels permutation14 hz
    mixedMoment B raw7646step2 raw7646step2Labels = mixedMoment B raw7646step3 raw7646step3Labels := by
      have ha : raw7646step3 = (fun i j => raw7646step2 (permutation2 i) (permutation7 j)) := by apply Matrix.ext; unfold raw7646step3 raw7646step2; decide +kernel
      have hl : raw7646step3Labels = raw7646step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7646step2 raw7646step2Labels permutation2 permutation7
    mixedMoment B raw7646step3 raw7646step3Labels = mixedMoment B raw7646step4 raw7646step4Labels := by
      have ha : raw7646step4 = raw7646step3 := by apply Matrix.ext; unfold raw7646step4 raw7646step3; decide +kernel
      have hl : raw7646step3Labels = labelEmbedding10 ∘ raw7646step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7646step3 raw7646step3Labels raw7646step4Labels labelEmbedding10 hl
    _ = mixedMoment B node5308 node5308Labels := by rfl

def raw7647 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw7647Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7647step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw7647step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7647step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw7647step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7647step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-3, 1, 2]]
def raw7647step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7647step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![2, 1, -3]]
def raw7647step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7647 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7647 raw7647Labels = mixedMoment B node5305 node5305Labels := by
  calc
    mixedMoment B raw7647 raw7647Labels = mixedMoment B raw7647step0 raw7647step0Labels := by
      have hz : ∀ j, raw7647 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7647step0 = (fun i j => raw7647 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7647step0 raw7647; decide +kernel
      have hl : raw7647step0Labels = raw7647Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7647 raw7647Labels permutation434 hz
    mixedMoment B raw7647step0 raw7647step0Labels = mixedMoment B raw7647step1 raw7647step1Labels := by
      have hz : ∀ j, raw7647step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7647step1 = (fun i j => raw7647step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7647step1 raw7647step0; decide +kernel
      have hl : raw7647step1Labels = raw7647step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7647step0 raw7647step0Labels permutation80 hz
    mixedMoment B raw7647step1 raw7647step1Labels = mixedMoment B raw7647step2 raw7647step2Labels := by
      have hz : ∀ j, raw7647step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw7647step2 = (fun i j => raw7647step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw7647step2 raw7647step1; decide +kernel
      have hl : raw7647step2Labels = raw7647step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7647step1 raw7647step1Labels permutation14 hz
    mixedMoment B raw7647step2 raw7647step2Labels = mixedMoment B raw7647step3 raw7647step3Labels := by
      have ha : raw7647step3 = (fun i j => raw7647step2 (permutation7 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7647step3 raw7647step2; decide +kernel
      have hl : raw7647step3Labels = raw7647step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7647step2 raw7647step2Labels permutation7 permutation2
    _ = mixedMoment B node5305 node5305Labels := by rfl

def raw7648 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw7648Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7648step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw7648step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7648step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw7648step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7648step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw7648step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw7648step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw7648step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7648 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7648 raw7648Labels = mixedMoment B node4896 node4896Labels := by
  calc
    mixedMoment B raw7648 raw7648Labels = mixedMoment B raw7648step0 raw7648step0Labels := by
      have hz : ∀ j, raw7648 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7648step0 = (fun i j => raw7648 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7648step0 raw7648; decide +kernel
      have hl : raw7648step0Labels = raw7648Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7648 raw7648Labels permutation434 hz
    mixedMoment B raw7648step0 raw7648step0Labels = mixedMoment B raw7648step1 raw7648step1Labels := by
      have hz : ∀ j, raw7648step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7648step1 = (fun i j => raw7648step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7648step1 raw7648step0; decide +kernel
      have hl : raw7648step1Labels = raw7648step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7648step0 raw7648step0Labels permutation80 hz
    mixedMoment B raw7648step1 raw7648step1Labels = mixedMoment B raw7648step2 raw7648step2Labels := by
      have ha : raw7648step2 = (fun i j => raw7648step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw7648step2 raw7648step1; decide +kernel
      have hl : raw7648step2Labels = raw7648step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7648step1 raw7648step1Labels permutation8 permutation6
    mixedMoment B raw7648step2 raw7648step2Labels = mixedMoment B raw7648step3 raw7648step3Labels := by
      have ha : raw7648step3 = raw7648step2 := by apply Matrix.ext; unfold raw7648step3 raw7648step2; decide +kernel
      have hl : raw7648step2Labels = labelEmbedding9 ∘ raw7648step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7648step2 raw7648step2Labels raw7648step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4896 node4896Labels := by rfl

def raw7649 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw7649Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7649step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw7649step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7649step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw7649step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw7649step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw7649step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7649 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7649 raw7649Labels = mixedMoment B node5260 node5260Labels := by
  calc
    mixedMoment B raw7649 raw7649Labels = mixedMoment B raw7649step0 raw7649step0Labels := by
      have hz : ∀ j, raw7649 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7649step0 = (fun i j => raw7649 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7649step0 raw7649; decide +kernel
      have hl : raw7649step0Labels = raw7649Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7649 raw7649Labels permutation434 hz
    mixedMoment B raw7649step0 raw7649step0Labels = mixedMoment B raw7649step1 raw7649step1Labels := by
      have ha : raw7649step1 = (fun i j => raw7649step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw7649step1 raw7649step0; decide +kernel
      have hl : raw7649step1Labels = raw7649step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7649step0 raw7649step0Labels permutation38 permutation6
    mixedMoment B raw7649step1 raw7649step1Labels = mixedMoment B raw7649step2 raw7649step2Labels := by
      have ha : raw7649step2 = raw7649step1 := by apply Matrix.ext; unfold raw7649step2 raw7649step1; decide +kernel
      have hl : raw7649step1Labels = labelEmbedding9 ∘ raw7649step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7649step1 raw7649step1Labels raw7649step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5260 node5260Labels := by rfl

def raw7650 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw7650Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7650step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw7650step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7650step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw7650step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw7650step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw7650step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7650 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7650 raw7650Labels = mixedMoment B node5260 node5260Labels := by
  calc
    mixedMoment B raw7650 raw7650Labels = mixedMoment B raw7650step0 raw7650step0Labels := by
      have hz : ∀ j, raw7650 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7650step0 = (fun i j => raw7650 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7650step0 raw7650; decide +kernel
      have hl : raw7650step0Labels = raw7650Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7650 raw7650Labels permutation346 hz
    mixedMoment B raw7650step0 raw7650step0Labels = mixedMoment B raw7650step1 raw7650step1Labels := by
      have ha : raw7650step1 = (fun i j => raw7650step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw7650step1 raw7650step0; decide +kernel
      have hl : raw7650step1Labels = raw7650step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7650step0 raw7650step0Labels permutation38 permutation6
    mixedMoment B raw7650step1 raw7650step1Labels = mixedMoment B raw7650step2 raw7650step2Labels := by
      have ha : raw7650step2 = raw7650step1 := by apply Matrix.ext; unfold raw7650step2 raw7650step1; decide +kernel
      have hl : raw7650step1Labels = labelEmbedding9 ∘ raw7650step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7650step1 raw7650step1Labels raw7650step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5260 node5260Labels := by rfl

def raw7651 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7651Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7651step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7651step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7651step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7651step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7651step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7651step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw7651step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7651step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7651 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7651 raw7651Labels = mixedMoment B node5294 node5294Labels := by
  calc
    mixedMoment B raw7651 raw7651Labels = mixedMoment B raw7651step0 raw7651step0Labels := by
      have hz : ∀ j, raw7651 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7651step0 = (fun i j => raw7651 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7651step0 raw7651; decide +kernel
      have hl : raw7651step0Labels = raw7651Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7651 raw7651Labels permutation434 hz
    mixedMoment B raw7651step0 raw7651step0Labels = mixedMoment B raw7651step1 raw7651step1Labels := by
      have hz : ∀ j, raw7651step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7651step1 = (fun i j => raw7651step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7651step1 raw7651step0; decide +kernel
      have hl : raw7651step1Labels = raw7651step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7651step0 raw7651step0Labels permutation80 hz
    mixedMoment B raw7651step1 raw7651step1Labels = mixedMoment B raw7651step2 raw7651step2Labels := by
      have ha : raw7651step2 = (fun i j => raw7651step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw7651step2 raw7651step1; decide +kernel
      have hl : raw7651step2Labels = raw7651step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7651step1 raw7651step1Labels permutation8 permutation6
    mixedMoment B raw7651step2 raw7651step2Labels = mixedMoment B raw7651step3 raw7651step3Labels := by
      have ha : raw7651step3 = raw7651step2 := by apply Matrix.ext; unfold raw7651step3 raw7651step2; decide +kernel
      have hl : raw7651step2Labels = labelEmbedding9 ∘ raw7651step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7651step2 raw7651step2Labels raw7651step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5294 node5294Labels := by rfl

def raw7652 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw7652Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7652step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw7652step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7652step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw7652step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7652step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw7652step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw7652step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw7652step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7652 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7652 raw7652Labels = mixedMoment B node5295 node5295Labels := by
  calc
    mixedMoment B raw7652 raw7652Labels = mixedMoment B raw7652step0 raw7652step0Labels := by
      have hz : ∀ j, raw7652 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7652step0 = (fun i j => raw7652 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7652step0 raw7652; decide +kernel
      have hl : raw7652step0Labels = raw7652Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7652 raw7652Labels permutation434 hz
    mixedMoment B raw7652step0 raw7652step0Labels = mixedMoment B raw7652step1 raw7652step1Labels := by
      have hz : ∀ j, raw7652step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7652step1 = (fun i j => raw7652step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7652step1 raw7652step0; decide +kernel
      have hl : raw7652step1Labels = raw7652step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7652step0 raw7652step0Labels permutation80 hz
    mixedMoment B raw7652step1 raw7652step1Labels = mixedMoment B raw7652step2 raw7652step2Labels := by
      have ha : raw7652step2 = (fun i j => raw7652step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw7652step2 raw7652step1; decide +kernel
      have hl : raw7652step2Labels = raw7652step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7652step1 raw7652step1Labels permutation8 permutation6
    mixedMoment B raw7652step2 raw7652step2Labels = mixedMoment B raw7652step3 raw7652step3Labels := by
      have ha : raw7652step3 = raw7652step2 := by apply Matrix.ext; unfold raw7652step3 raw7652step2; decide +kernel
      have hl : raw7652step2Labels = labelEmbedding9 ∘ raw7652step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7652step2 raw7652step2Labels raw7652step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5295 node5295Labels := by rfl

def raw7653 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw7653Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7653step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw7653step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7653step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw7653step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7653step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw7653step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw7653step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw7653step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7653 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7653 raw7653Labels = mixedMoment B node4896 node4896Labels := by
  calc
    mixedMoment B raw7653 raw7653Labels = mixedMoment B raw7653step0 raw7653step0Labels := by
      have hz : ∀ j, raw7653 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7653step0 = (fun i j => raw7653 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7653step0 raw7653; decide +kernel
      have hl : raw7653step0Labels = raw7653Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7653 raw7653Labels permutation434 hz
    mixedMoment B raw7653step0 raw7653step0Labels = mixedMoment B raw7653step1 raw7653step1Labels := by
      have hz : ∀ j, raw7653step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7653step1 = (fun i j => raw7653step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7653step1 raw7653step0; decide +kernel
      have hl : raw7653step1Labels = raw7653step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7653step0 raw7653step0Labels permutation56 hz
    mixedMoment B raw7653step1 raw7653step1Labels = mixedMoment B raw7653step2 raw7653step2Labels := by
      have ha : raw7653step2 = (fun i j => raw7653step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw7653step2 raw7653step1; decide +kernel
      have hl : raw7653step2Labels = raw7653step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7653step1 raw7653step1Labels permutation8 permutation6
    mixedMoment B raw7653step2 raw7653step2Labels = mixedMoment B raw7653step3 raw7653step3Labels := by
      have ha : raw7653step3 = raw7653step2 := by apply Matrix.ext; unfold raw7653step3 raw7653step2; decide +kernel
      have hl : raw7653step2Labels = labelEmbedding9 ∘ raw7653step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7653step2 raw7653step2Labels raw7653step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4896 node4896Labels := by rfl

def raw7654 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw7654Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7654step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw7654step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7654step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw7654step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw7654step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw7654step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7654 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7654 raw7654Labels = mixedMoment B node5260 node5260Labels := by
  calc
    mixedMoment B raw7654 raw7654Labels = mixedMoment B raw7654step0 raw7654step0Labels := by
      have hz : ∀ j, raw7654 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw7654step0 = (fun i j => raw7654 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw7654step0 raw7654; decide +kernel
      have hl : raw7654step0Labels = raw7654Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7654 raw7654Labels permutation265 hz
    mixedMoment B raw7654step0 raw7654step0Labels = mixedMoment B raw7654step1 raw7654step1Labels := by
      have ha : raw7654step1 = (fun i j => raw7654step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw7654step1 raw7654step0; decide +kernel
      have hl : raw7654step1Labels = raw7654step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7654step0 raw7654step0Labels permutation38 permutation6
    mixedMoment B raw7654step1 raw7654step1Labels = mixedMoment B raw7654step2 raw7654step2Labels := by
      have ha : raw7654step2 = raw7654step1 := by apply Matrix.ext; unfold raw7654step2 raw7654step1; decide +kernel
      have hl : raw7654step1Labels = labelEmbedding9 ∘ raw7654step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7654step1 raw7654step1Labels raw7654step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5260 node5260Labels := by rfl

def raw7655 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw7655Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7655step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw7655step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7655step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw7655step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7655step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw7655step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw7655step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw7655step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7655 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7655 raw7655Labels = mixedMoment B node5295 node5295Labels := by
  calc
    mixedMoment B raw7655 raw7655Labels = mixedMoment B raw7655step0 raw7655step0Labels := by
      have hz : ∀ j, raw7655 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7655step0 = (fun i j => raw7655 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7655step0 raw7655; decide +kernel
      have hl : raw7655step0Labels = raw7655Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7655 raw7655Labels permutation434 hz
    mixedMoment B raw7655step0 raw7655step0Labels = mixedMoment B raw7655step1 raw7655step1Labels := by
      have hz : ∀ j, raw7655step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7655step1 = (fun i j => raw7655step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7655step1 raw7655step0; decide +kernel
      have hl : raw7655step1Labels = raw7655step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7655step0 raw7655step0Labels permutation56 hz
    mixedMoment B raw7655step1 raw7655step1Labels = mixedMoment B raw7655step2 raw7655step2Labels := by
      have ha : raw7655step2 = (fun i j => raw7655step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw7655step2 raw7655step1; decide +kernel
      have hl : raw7655step2Labels = raw7655step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7655step1 raw7655step1Labels permutation8 permutation6
    mixedMoment B raw7655step2 raw7655step2Labels = mixedMoment B raw7655step3 raw7655step3Labels := by
      have ha : raw7655step3 = raw7655step2 := by apply Matrix.ext; unfold raw7655step3 raw7655step2; decide +kernel
      have hl : raw7655step2Labels = labelEmbedding9 ∘ raw7655step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7655step2 raw7655step2Labels raw7655step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5295 node5295Labels := by rfl

def raw7656 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw7656Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7656step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw7656step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7656step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw7656step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7656step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, 3, -3], ![1, -2, 1], ![-1, -1, 2]]
def raw7656step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7656step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![-1, -1, 2], ![-2, 1, 1]]
def raw7656step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw7656step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![2, -1, -1]]
def raw7656step4Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw7656step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![2, -1, -1]]
def raw7656step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7656 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7656 raw7656Labels = mixedMoment B node4901 node4901Labels := by
  calc
    mixedMoment B raw7656 raw7656Labels = mixedMoment B raw7656step0 raw7656step0Labels := by
      have hz : ∀ j, raw7656 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7656step0 = (fun i j => raw7656 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7656step0 raw7656; decide +kernel
      have hl : raw7656step0Labels = raw7656Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7656 raw7656Labels permutation434 hz
    mixedMoment B raw7656step0 raw7656step0Labels = mixedMoment B raw7656step1 raw7656step1Labels := by
      have hz : ∀ j, raw7656step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7656step1 = (fun i j => raw7656step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7656step1 raw7656step0; decide +kernel
      have hl : raw7656step1Labels = raw7656step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7656step0 raw7656step0Labels permutation80 hz
    mixedMoment B raw7656step1 raw7656step1Labels = mixedMoment B raw7656step2 raw7656step2Labels := by
      have hz : ∀ j, raw7656step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw7656step2 = (fun i j => raw7656step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw7656step2 raw7656step1; decide +kernel
      have hl : raw7656step2Labels = raw7656step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7656step1 raw7656step1Labels permutation14 hz
    mixedMoment B raw7656step2 raw7656step2Labels = mixedMoment B raw7656step3 raw7656step3Labels := by
      have ha : raw7656step3 = (fun i j => raw7656step2 (permutation3 i) (permutation4 j)) := by apply Matrix.ext; unfold raw7656step3 raw7656step2; decide +kernel
      have hl : raw7656step3Labels = raw7656step2Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7656step2 raw7656step2Labels permutation3 permutation4
    mixedMoment B raw7656step3 raw7656step3Labels = mixedMoment B raw7656step4 raw7656step4Labels := by
      have ha : raw7656step4 = -raw7656step3 := by apply Matrix.ext; change ∀ i j, raw7656step4 i j = -(raw7656step3 i j); unfold raw7656step4 raw7656step3; decide +kernel
      have hl : raw7656step4Labels = raw7656step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7656step4 raw7656step4Labels = mixedMoment B raw7656step5 raw7656step5Labels := by
      have ha : raw7656step5 = raw7656step4 := by apply Matrix.ext; unfold raw7656step5 raw7656step4; decide +kernel
      have hl : raw7656step4Labels = labelEmbedding7 ∘ raw7656step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7656step4 raw7656step4Labels raw7656step5Labels labelEmbedding7 hl
    _ = mixedMoment B node4901 node4901Labels := by rfl

def raw7657 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw7657Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7657step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw7657step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7657step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw7657step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7657step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw7657step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw7657step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw7657step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7657 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7657 raw7657Labels = mixedMoment B node5275 node5275Labels := by
  calc
    mixedMoment B raw7657 raw7657Labels = mixedMoment B raw7657step0 raw7657step0Labels := by
      have hz : ∀ j, raw7657 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7657step0 = (fun i j => raw7657 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7657step0 raw7657; decide +kernel
      have hl : raw7657step0Labels = raw7657Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7657 raw7657Labels permutation434 hz
    mixedMoment B raw7657step0 raw7657step0Labels = mixedMoment B raw7657step1 raw7657step1Labels := by
      have hz : ∀ j, raw7657step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7657step1 = (fun i j => raw7657step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7657step1 raw7657step0; decide +kernel
      have hl : raw7657step1Labels = raw7657step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7657step0 raw7657step0Labels permutation56 hz
    mixedMoment B raw7657step1 raw7657step1Labels = mixedMoment B raw7657step2 raw7657step2Labels := by
      have ha : raw7657step2 = (fun i j => raw7657step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw7657step2 raw7657step1; decide +kernel
      have hl : raw7657step2Labels = raw7657step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7657step1 raw7657step1Labels permutation8 permutation6
    mixedMoment B raw7657step2 raw7657step2Labels = mixedMoment B raw7657step3 raw7657step3Labels := by
      have ha : raw7657step3 = raw7657step2 := by apply Matrix.ext; unfold raw7657step3 raw7657step2; decide +kernel
      have hl : raw7657step2Labels = labelEmbedding9 ∘ raw7657step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7657step2 raw7657step2Labels raw7657step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5275 node5275Labels := by rfl

def raw7658 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw7658Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7658step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw7658step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7658step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw7658step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7658step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw7658step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw7658step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw7658step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7658 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7658 raw7658Labels = mixedMoment B node5275 node5275Labels := by
  calc
    mixedMoment B raw7658 raw7658Labels = mixedMoment B raw7658step0 raw7658step0Labels := by
      have hz : ∀ j, raw7658 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7658step0 = (fun i j => raw7658 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7658step0 raw7658; decide +kernel
      have hl : raw7658step0Labels = raw7658Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7658 raw7658Labels permutation346 hz
    mixedMoment B raw7658step0 raw7658step0Labels = mixedMoment B raw7658step1 raw7658step1Labels := by
      have hz : ∀ j, raw7658step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7658step1 = (fun i j => raw7658step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7658step1 raw7658step0; decide +kernel
      have hl : raw7658step1Labels = raw7658step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7658step0 raw7658step0Labels permutation56 hz
    mixedMoment B raw7658step1 raw7658step1Labels = mixedMoment B raw7658step2 raw7658step2Labels := by
      have ha : raw7658step2 = (fun i j => raw7658step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw7658step2 raw7658step1; decide +kernel
      have hl : raw7658step2Labels = raw7658step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7658step1 raw7658step1Labels permutation8 permutation6
    mixedMoment B raw7658step2 raw7658step2Labels = mixedMoment B raw7658step3 raw7658step3Labels := by
      have ha : raw7658step3 = raw7658step2 := by apply Matrix.ext; unfold raw7658step3 raw7658step2; decide +kernel
      have hl : raw7658step2Labels = labelEmbedding9 ∘ raw7658step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7658step2 raw7658step2Labels raw7658step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5275 node5275Labels := by rfl

def raw7659 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw7659Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7659step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw7659step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7659step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw7659step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7659step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 2, -3], ![0, -1, 1], ![-1, -1, 2]]
def raw7659step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7659step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![2, -1, -1]]
def raw7659step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw7659step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![2, -1, -1]]
def raw7659step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7659 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7659 raw7659Labels = mixedMoment B node5309 node5309Labels := by
  calc
    mixedMoment B raw7659 raw7659Labels = mixedMoment B raw7659step0 raw7659step0Labels := by
      have hz : ∀ j, raw7659 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7659step0 = (fun i j => raw7659 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7659step0 raw7659; decide +kernel
      have hl : raw7659step0Labels = raw7659Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7659 raw7659Labels permutation434 hz
    mixedMoment B raw7659step0 raw7659step0Labels = mixedMoment B raw7659step1 raw7659step1Labels := by
      have hz : ∀ j, raw7659step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7659step1 = (fun i j => raw7659step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7659step1 raw7659step0; decide +kernel
      have hl : raw7659step1Labels = raw7659step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7659step0 raw7659step0Labels permutation80 hz
    mixedMoment B raw7659step1 raw7659step1Labels = mixedMoment B raw7659step2 raw7659step2Labels := by
      have hz : ∀ j, raw7659step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw7659step2 = (fun i j => raw7659step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw7659step2 raw7659step1; decide +kernel
      have hl : raw7659step2Labels = raw7659step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7659step1 raw7659step1Labels permutation14 hz
    mixedMoment B raw7659step2 raw7659step2Labels = mixedMoment B raw7659step3 raw7659step3Labels := by
      have ha : raw7659step3 = (fun i j => raw7659step2 (permutation2 i) (permutation6 j)) := by apply Matrix.ext; unfold raw7659step3 raw7659step2; decide +kernel
      have hl : raw7659step3Labels = raw7659step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7659step2 raw7659step2Labels permutation2 permutation6
    mixedMoment B raw7659step3 raw7659step3Labels = mixedMoment B raw7659step4 raw7659step4Labels := by
      have ha : raw7659step4 = raw7659step3 := by apply Matrix.ext; unfold raw7659step4 raw7659step3; decide +kernel
      have hl : raw7659step3Labels = labelEmbedding9 ∘ raw7659step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7659step3 raw7659step3Labels raw7659step4Labels labelEmbedding9 hl
    _ = mixedMoment B node5309 node5309Labels := by rfl

def raw7660 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw7660Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7660step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw7660step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7660step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw7660step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7660step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw7660step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7660 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7660 raw7660Labels = mixedMoment B node3103 node3103Labels := by
  calc
    mixedMoment B raw7660 raw7660Labels = mixedMoment B raw7660step0 raw7660step0Labels := by
      have hz : ∀ j, raw7660 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7660step0 = (fun i j => raw7660 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7660step0 raw7660; decide +kernel
      have hl : raw7660step0Labels = raw7660Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7660 raw7660Labels permutation434 hz
    mixedMoment B raw7660step0 raw7660step0Labels = mixedMoment B raw7660step1 raw7660step1Labels := by
      have hz : ∀ j, raw7660step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7660step1 = (fun i j => raw7660step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7660step1 raw7660step0; decide +kernel
      have hl : raw7660step1Labels = raw7660step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7660step0 raw7660step0Labels permutation56 hz
    mixedMoment B raw7660step1 raw7660step1Labels = mixedMoment B raw7660step2 raw7660step2Labels := by
      have ha : raw7660step2 = (fun i j => raw7660step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw7660step2 raw7660step1; decide +kernel
      have hl : raw7660step2Labels = raw7660step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7660step1 raw7660step1Labels permutation8 permutation6
    _ = mixedMoment B node3103 node3103Labels := by rfl

def raw7661 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw7661Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7661step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw7661step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7661step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw7661step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7661step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw7661step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7661 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7661 raw7661Labels = mixedMoment B node3103 node3103Labels := by
  calc
    mixedMoment B raw7661 raw7661Labels = mixedMoment B raw7661step0 raw7661step0Labels := by
      have hz : ∀ j, raw7661 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7661step0 = (fun i j => raw7661 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7661step0 raw7661; decide +kernel
      have hl : raw7661step0Labels = raw7661Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7661 raw7661Labels permutation346 hz
    mixedMoment B raw7661step0 raw7661step0Labels = mixedMoment B raw7661step1 raw7661step1Labels := by
      have hz : ∀ j, raw7661step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7661step1 = (fun i j => raw7661step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7661step1 raw7661step0; decide +kernel
      have hl : raw7661step1Labels = raw7661step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7661step0 raw7661step0Labels permutation56 hz
    mixedMoment B raw7661step1 raw7661step1Labels = mixedMoment B raw7661step2 raw7661step2Labels := by
      have ha : raw7661step2 = (fun i j => raw7661step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw7661step2 raw7661step1; decide +kernel
      have hl : raw7661step2Labels = raw7661step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7661step1 raw7661step1Labels permutation8 permutation6
    _ = mixedMoment B node3103 node3103Labels := by rfl

def raw7662 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7662Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7662step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7662step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7662step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7662step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7662step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![-2, 0, 2]]
def raw7662step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7662step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![2, -2, 0]]
def raw7662step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7662 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7662 raw7662Labels = mixedMoment B node3124 node3124Labels := by
  calc
    mixedMoment B raw7662 raw7662Labels = mixedMoment B raw7662step0 raw7662step0Labels := by
      have hz : ∀ j, raw7662 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7662step0 = (fun i j => raw7662 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7662step0 raw7662; decide +kernel
      have hl : raw7662step0Labels = raw7662Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7662 raw7662Labels permutation434 hz
    mixedMoment B raw7662step0 raw7662step0Labels = mixedMoment B raw7662step1 raw7662step1Labels := by
      have hz : ∀ j, raw7662step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7662step1 = (fun i j => raw7662step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7662step1 raw7662step0; decide +kernel
      have hl : raw7662step1Labels = raw7662step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7662step0 raw7662step0Labels permutation80 hz
    mixedMoment B raw7662step1 raw7662step1Labels = mixedMoment B raw7662step2 raw7662step2Labels := by
      have hz : ∀ j, raw7662step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw7662step2 = (fun i j => raw7662step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw7662step2 raw7662step1; decide +kernel
      have hl : raw7662step2Labels = raw7662step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7662step1 raw7662step1Labels permutation14 hz
    mixedMoment B raw7662step2 raw7662step2Labels = mixedMoment B raw7662step3 raw7662step3Labels := by
      have ha : raw7662step3 = (fun i j => raw7662step2 (permutation2 i) (permutation6 j)) := by apply Matrix.ext; unfold raw7662step3 raw7662step2; decide +kernel
      have hl : raw7662step3Labels = raw7662step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7662step2 raw7662step2Labels permutation2 permutation6
    _ = mixedMoment B node3124 node3124Labels := by rfl

def raw7663 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw7663Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7663step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw7663step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7663step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw7663step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7663step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-3, 1, 2]]
def raw7663step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7663step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 1, -2], ![2, -3, 1]]
def raw7663step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7663 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7663 raw7663Labels = mixedMoment B node3125 node3125Labels := by
  calc
    mixedMoment B raw7663 raw7663Labels = mixedMoment B raw7663step0 raw7663step0Labels := by
      have hz : ∀ j, raw7663 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7663step0 = (fun i j => raw7663 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7663step0 raw7663; decide +kernel
      have hl : raw7663step0Labels = raw7663Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7663 raw7663Labels permutation434 hz
    mixedMoment B raw7663step0 raw7663step0Labels = mixedMoment B raw7663step1 raw7663step1Labels := by
      have hz : ∀ j, raw7663step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7663step1 = (fun i j => raw7663step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7663step1 raw7663step0; decide +kernel
      have hl : raw7663step1Labels = raw7663step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7663step0 raw7663step0Labels permutation80 hz
    mixedMoment B raw7663step1 raw7663step1Labels = mixedMoment B raw7663step2 raw7663step2Labels := by
      have hz : ∀ j, raw7663step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw7663step2 = (fun i j => raw7663step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw7663step2 raw7663step1; decide +kernel
      have hl : raw7663step2Labels = raw7663step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7663step1 raw7663step1Labels permutation14 hz
    mixedMoment B raw7663step2 raw7663step2Labels = mixedMoment B raw7663step3 raw7663step3Labels := by
      have ha : raw7663step3 = (fun i j => raw7663step2 (permutation7 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7663step3 raw7663step2; decide +kernel
      have hl : raw7663step3Labels = raw7663step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7663step2 raw7663step2Labels permutation7 permutation3
    _ = mixedMoment B node3125 node3125Labels := by rfl

def raw7664 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw7664Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7664step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw7664step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7664step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw7664step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7664step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw7664step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7664 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7664 raw7664Labels = mixedMoment B node2266 node2266Labels := by
  calc
    mixedMoment B raw7664 raw7664Labels = mixedMoment B raw7664step0 raw7664step0Labels := by
      have hz : ∀ j, raw7664 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7664step0 = (fun i j => raw7664 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7664step0 raw7664; decide +kernel
      have hl : raw7664step0Labels = raw7664Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7664 raw7664Labels permutation434 hz
    mixedMoment B raw7664step0 raw7664step0Labels = mixedMoment B raw7664step1 raw7664step1Labels := by
      have hz : ∀ j, raw7664step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7664step1 = (fun i j => raw7664step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7664step1 raw7664step0; decide +kernel
      have hl : raw7664step1Labels = raw7664step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7664step0 raw7664step0Labels permutation80 hz
    mixedMoment B raw7664step1 raw7664step1Labels = mixedMoment B raw7664step2 raw7664step2Labels := by
      have ha : raw7664step2 = (fun i j => raw7664step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw7664step2 raw7664step1; decide +kernel
      have hl : raw7664step2Labels = raw7664step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7664step1 raw7664step1Labels permutation8 permutation6
    _ = mixedMoment B node2266 node2266Labels := by rfl

def raw7665 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw7665Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7665step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw7665step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7665step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw7665step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7665 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7665 raw7665Labels = mixedMoment B node2724 node2724Labels := by
  calc
    mixedMoment B raw7665 raw7665Labels = mixedMoment B raw7665step0 raw7665step0Labels := by
      have hz : ∀ j, raw7665 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7665step0 = (fun i j => raw7665 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7665step0 raw7665; decide +kernel
      have hl : raw7665step0Labels = raw7665Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7665 raw7665Labels permutation434 hz
    mixedMoment B raw7665step0 raw7665step0Labels = mixedMoment B raw7665step1 raw7665step1Labels := by
      have ha : raw7665step1 = (fun i j => raw7665step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw7665step1 raw7665step0; decide +kernel
      have hl : raw7665step1Labels = raw7665step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7665step0 raw7665step0Labels permutation38 permutation6
    _ = mixedMoment B node2724 node2724Labels := by rfl

def raw7666 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw7666Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7666step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw7666step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7666step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw7666step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7666 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7666 raw7666Labels = mixedMoment B node2724 node2724Labels := by
  calc
    mixedMoment B raw7666 raw7666Labels = mixedMoment B raw7666step0 raw7666step0Labels := by
      have hz : ∀ j, raw7666 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7666step0 = (fun i j => raw7666 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7666step0 raw7666; decide +kernel
      have hl : raw7666step0Labels = raw7666Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7666 raw7666Labels permutation346 hz
    mixedMoment B raw7666step0 raw7666step0Labels = mixedMoment B raw7666step1 raw7666step1Labels := by
      have ha : raw7666step1 = (fun i j => raw7666step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw7666step1 raw7666step0; decide +kernel
      have hl : raw7666step1Labels = raw7666step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7666step0 raw7666step0Labels permutation38 permutation6
    _ = mixedMoment B node2724 node2724Labels := by rfl

def raw7667 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7667Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7667step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7667step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7667step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7667step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7667step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7667step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7667 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7667 raw7667Labels = mixedMoment B node2768 node2768Labels := by
  calc
    mixedMoment B raw7667 raw7667Labels = mixedMoment B raw7667step0 raw7667step0Labels := by
      have hz : ∀ j, raw7667 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7667step0 = (fun i j => raw7667 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7667step0 raw7667; decide +kernel
      have hl : raw7667step0Labels = raw7667Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7667 raw7667Labels permutation434 hz
    mixedMoment B raw7667step0 raw7667step0Labels = mixedMoment B raw7667step1 raw7667step1Labels := by
      have hz : ∀ j, raw7667step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7667step1 = (fun i j => raw7667step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7667step1 raw7667step0; decide +kernel
      have hl : raw7667step1Labels = raw7667step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7667step0 raw7667step0Labels permutation80 hz
    mixedMoment B raw7667step1 raw7667step1Labels = mixedMoment B raw7667step2 raw7667step2Labels := by
      have ha : raw7667step2 = (fun i j => raw7667step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw7667step2 raw7667step1; decide +kernel
      have hl : raw7667step2Labels = raw7667step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7667step1 raw7667step1Labels permutation8 permutation6
    _ = mixedMoment B node2768 node2768Labels := by rfl

def raw7668 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw7668Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7668step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw7668step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7668step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw7668step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7668step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw7668step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7668 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7668 raw7668Labels = mixedMoment B node2769 node2769Labels := by
  calc
    mixedMoment B raw7668 raw7668Labels = mixedMoment B raw7668step0 raw7668step0Labels := by
      have hz : ∀ j, raw7668 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7668step0 = (fun i j => raw7668 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7668step0 raw7668; decide +kernel
      have hl : raw7668step0Labels = raw7668Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7668 raw7668Labels permutation434 hz
    mixedMoment B raw7668step0 raw7668step0Labels = mixedMoment B raw7668step1 raw7668step1Labels := by
      have hz : ∀ j, raw7668step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7668step1 = (fun i j => raw7668step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7668step1 raw7668step0; decide +kernel
      have hl : raw7668step1Labels = raw7668step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7668step0 raw7668step0Labels permutation80 hz
    mixedMoment B raw7668step1 raw7668step1Labels = mixedMoment B raw7668step2 raw7668step2Labels := by
      have ha : raw7668step2 = (fun i j => raw7668step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw7668step2 raw7668step1; decide +kernel
      have hl : raw7668step2Labels = raw7668step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7668step1 raw7668step1Labels permutation8 permutation6
    _ = mixedMoment B node2769 node2769Labels := by rfl

def raw7669 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw7669Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7669step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw7669step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7669step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw7669step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7669step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw7669step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7669 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7669 raw7669Labels = mixedMoment B node2266 node2266Labels := by
  calc
    mixedMoment B raw7669 raw7669Labels = mixedMoment B raw7669step0 raw7669step0Labels := by
      have hz : ∀ j, raw7669 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7669step0 = (fun i j => raw7669 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7669step0 raw7669; decide +kernel
      have hl : raw7669step0Labels = raw7669Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7669 raw7669Labels permutation434 hz
    mixedMoment B raw7669step0 raw7669step0Labels = mixedMoment B raw7669step1 raw7669step1Labels := by
      have hz : ∀ j, raw7669step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7669step1 = (fun i j => raw7669step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7669step1 raw7669step0; decide +kernel
      have hl : raw7669step1Labels = raw7669step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7669step0 raw7669step0Labels permutation56 hz
    mixedMoment B raw7669step1 raw7669step1Labels = mixedMoment B raw7669step2 raw7669step2Labels := by
      have ha : raw7669step2 = (fun i j => raw7669step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw7669step2 raw7669step1; decide +kernel
      have hl : raw7669step2Labels = raw7669step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7669step1 raw7669step1Labels permutation8 permutation6
    _ = mixedMoment B node2266 node2266Labels := by rfl

def raw7670 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw7670Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7670step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw7670step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7670step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw7670step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7670 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7670 raw7670Labels = mixedMoment B node2724 node2724Labels := by
  calc
    mixedMoment B raw7670 raw7670Labels = mixedMoment B raw7670step0 raw7670step0Labels := by
      have hz : ∀ j, raw7670 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw7670step0 = (fun i j => raw7670 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw7670step0 raw7670; decide +kernel
      have hl : raw7670step0Labels = raw7670Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7670 raw7670Labels permutation265 hz
    mixedMoment B raw7670step0 raw7670step0Labels = mixedMoment B raw7670step1 raw7670step1Labels := by
      have ha : raw7670step1 = (fun i j => raw7670step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw7670step1 raw7670step0; decide +kernel
      have hl : raw7670step1Labels = raw7670step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7670step0 raw7670step0Labels permutation38 permutation6
    _ = mixedMoment B node2724 node2724Labels := by rfl

def raw7671 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw7671Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7671step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw7671step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7671step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw7671step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7671step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw7671step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7671 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7671 raw7671Labels = mixedMoment B node2769 node2769Labels := by
  calc
    mixedMoment B raw7671 raw7671Labels = mixedMoment B raw7671step0 raw7671step0Labels := by
      have hz : ∀ j, raw7671 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7671step0 = (fun i j => raw7671 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7671step0 raw7671; decide +kernel
      have hl : raw7671step0Labels = raw7671Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7671 raw7671Labels permutation434 hz
    mixedMoment B raw7671step0 raw7671step0Labels = mixedMoment B raw7671step1 raw7671step1Labels := by
      have hz : ∀ j, raw7671step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7671step1 = (fun i j => raw7671step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7671step1 raw7671step0; decide +kernel
      have hl : raw7671step1Labels = raw7671step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7671step0 raw7671step0Labels permutation56 hz
    mixedMoment B raw7671step1 raw7671step1Labels = mixedMoment B raw7671step2 raw7671step2Labels := by
      have ha : raw7671step2 = (fun i j => raw7671step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw7671step2 raw7671step1; decide +kernel
      have hl : raw7671step2Labels = raw7671step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7671step1 raw7671step1Labels permutation8 permutation6
    _ = mixedMoment B node2769 node2769Labels := by rfl

def raw7672 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw7672Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7672step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw7672step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7672step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw7672step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7672step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, 3, -3], ![1, -2, 1], ![-1, -1, 2]]
def raw7672step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7672step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![2, -1, -1]]
def raw7672step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7672 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7672 raw7672Labels = mixedMoment B node2293 node2293Labels := by
  calc
    mixedMoment B raw7672 raw7672Labels = mixedMoment B raw7672step0 raw7672step0Labels := by
      have hz : ∀ j, raw7672 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7672step0 = (fun i j => raw7672 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7672step0 raw7672; decide +kernel
      have hl : raw7672step0Labels = raw7672Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7672 raw7672Labels permutation434 hz
    mixedMoment B raw7672step0 raw7672step0Labels = mixedMoment B raw7672step1 raw7672step1Labels := by
      have hz : ∀ j, raw7672step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7672step1 = (fun i j => raw7672step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7672step1 raw7672step0; decide +kernel
      have hl : raw7672step1Labels = raw7672step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7672step0 raw7672step0Labels permutation80 hz
    mixedMoment B raw7672step1 raw7672step1Labels = mixedMoment B raw7672step2 raw7672step2Labels := by
      have hz : ∀ j, raw7672step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw7672step2 = (fun i j => raw7672step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw7672step2 raw7672step1; decide +kernel
      have hl : raw7672step2Labels = raw7672step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7672step1 raw7672step1Labels permutation14 hz
    mixedMoment B raw7672step2 raw7672step2Labels = mixedMoment B raw7672step3 raw7672step3Labels := by
      have ha : raw7672step3 = (fun i j => raw7672step2 (permutation2 i) (permutation6 j)) := by apply Matrix.ext; unfold raw7672step3 raw7672step2; decide +kernel
      have hl : raw7672step3Labels = raw7672step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7672step2 raw7672step2Labels permutation2 permutation6
    _ = mixedMoment B node2293 node2293Labels := by rfl

def raw7673 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw7673Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7673step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw7673step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7673step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw7673step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7673step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw7673step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7673 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7673 raw7673Labels = mixedMoment B node2743 node2743Labels := by
  calc
    mixedMoment B raw7673 raw7673Labels = mixedMoment B raw7673step0 raw7673step0Labels := by
      have hz : ∀ j, raw7673 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7673step0 = (fun i j => raw7673 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7673step0 raw7673; decide +kernel
      have hl : raw7673step0Labels = raw7673Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7673 raw7673Labels permutation434 hz
    mixedMoment B raw7673step0 raw7673step0Labels = mixedMoment B raw7673step1 raw7673step1Labels := by
      have hz : ∀ j, raw7673step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7673step1 = (fun i j => raw7673step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7673step1 raw7673step0; decide +kernel
      have hl : raw7673step1Labels = raw7673step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7673step0 raw7673step0Labels permutation56 hz
    mixedMoment B raw7673step1 raw7673step1Labels = mixedMoment B raw7673step2 raw7673step2Labels := by
      have ha : raw7673step2 = (fun i j => raw7673step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw7673step2 raw7673step1; decide +kernel
      have hl : raw7673step2Labels = raw7673step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7673step1 raw7673step1Labels permutation8 permutation6
    _ = mixedMoment B node2743 node2743Labels := by rfl

def raw7674 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw7674Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7674step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw7674step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7674step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw7674step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7674step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw7674step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7674 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7674 raw7674Labels = mixedMoment B node2743 node2743Labels := by
  calc
    mixedMoment B raw7674 raw7674Labels = mixedMoment B raw7674step0 raw7674step0Labels := by
      have hz : ∀ j, raw7674 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7674step0 = (fun i j => raw7674 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7674step0 raw7674; decide +kernel
      have hl : raw7674step0Labels = raw7674Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7674 raw7674Labels permutation346 hz
    mixedMoment B raw7674step0 raw7674step0Labels = mixedMoment B raw7674step1 raw7674step1Labels := by
      have hz : ∀ j, raw7674step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7674step1 = (fun i j => raw7674step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7674step1 raw7674step0; decide +kernel
      have hl : raw7674step1Labels = raw7674step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7674step0 raw7674step0Labels permutation56 hz
    mixedMoment B raw7674step1 raw7674step1Labels = mixedMoment B raw7674step2 raw7674step2Labels := by
      have ha : raw7674step2 = (fun i j => raw7674step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw7674step2 raw7674step1; decide +kernel
      have hl : raw7674step2Labels = raw7674step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7674step1 raw7674step1Labels permutation8 permutation6
    _ = mixedMoment B node2743 node2743Labels := by rfl

def raw7675 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw7675Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7675step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw7675step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7675step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw7675step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7675step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 2, -3], ![0, -1, 1], ![-1, -1, 2]]
def raw7675step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7675step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![2, -1, -1]]
def raw7675step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7675 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7675 raw7675Labels = mixedMoment B node2787 node2787Labels := by
  calc
    mixedMoment B raw7675 raw7675Labels = mixedMoment B raw7675step0 raw7675step0Labels := by
      have hz : ∀ j, raw7675 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7675step0 = (fun i j => raw7675 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7675step0 raw7675; decide +kernel
      have hl : raw7675step0Labels = raw7675Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7675 raw7675Labels permutation434 hz
    mixedMoment B raw7675step0 raw7675step0Labels = mixedMoment B raw7675step1 raw7675step1Labels := by
      have hz : ∀ j, raw7675step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7675step1 = (fun i j => raw7675step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7675step1 raw7675step0; decide +kernel
      have hl : raw7675step1Labels = raw7675step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7675step0 raw7675step0Labels permutation80 hz
    mixedMoment B raw7675step1 raw7675step1Labels = mixedMoment B raw7675step2 raw7675step2Labels := by
      have hz : ∀ j, raw7675step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw7675step2 = (fun i j => raw7675step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw7675step2 raw7675step1; decide +kernel
      have hl : raw7675step2Labels = raw7675step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7675step1 raw7675step1Labels permutation14 hz
    mixedMoment B raw7675step2 raw7675step2Labels = mixedMoment B raw7675step3 raw7675step3Labels := by
      have ha : raw7675step3 = (fun i j => raw7675step2 (permutation2 i) (permutation6 j)) := by apply Matrix.ext; unfold raw7675step3 raw7675step2; decide +kernel
      have hl : raw7675step3Labels = raw7675step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7675step2 raw7675step2Labels permutation2 permutation6
    _ = mixedMoment B node2787 node2787Labels := by rfl

def raw7676 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw7676Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7676step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw7676step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7676step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw7676step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7676step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw7676step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7676step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw7676step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7676 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7676 raw7676Labels = mixedMoment B node2765 node2765Labels := by
  calc
    mixedMoment B raw7676 raw7676Labels = mixedMoment B raw7676step0 raw7676step0Labels := by
      have hz : ∀ j, raw7676 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7676step0 = (fun i j => raw7676 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7676step0 raw7676; decide +kernel
      have hl : raw7676step0Labels = raw7676Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7676 raw7676Labels permutation434 hz
    mixedMoment B raw7676step0 raw7676step0Labels = mixedMoment B raw7676step1 raw7676step1Labels := by
      have hz : ∀ j, raw7676step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7676step1 = (fun i j => raw7676step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7676step1 raw7676step0; decide +kernel
      have hl : raw7676step1Labels = raw7676step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7676step0 raw7676step0Labels permutation56 hz
    mixedMoment B raw7676step1 raw7676step1Labels = mixedMoment B raw7676step2 raw7676step2Labels := by
      have ha : raw7676step2 = (fun i j => raw7676step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw7676step2 raw7676step1; decide +kernel
      have hl : raw7676step2Labels = raw7676step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7676step1 raw7676step1Labels permutation8 permutation7
    mixedMoment B raw7676step2 raw7676step2Labels = mixedMoment B raw7676step3 raw7676step3Labels := by
      have ha : raw7676step3 = raw7676step2 := by apply Matrix.ext; unfold raw7676step3 raw7676step2; decide +kernel
      have hl : raw7676step2Labels = labelEmbedding1 ∘ raw7676step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7676step2 raw7676step2Labels raw7676step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2765 node2765Labels := by rfl

def raw7677 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw7677Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7677step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw7677step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7677step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw7677step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7677step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw7677step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7677step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw7677step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7677 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7677 raw7677Labels = mixedMoment B node2765 node2765Labels := by
  calc
    mixedMoment B raw7677 raw7677Labels = mixedMoment B raw7677step0 raw7677step0Labels := by
      have hz : ∀ j, raw7677 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7677step0 = (fun i j => raw7677 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7677step0 raw7677; decide +kernel
      have hl : raw7677step0Labels = raw7677Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7677 raw7677Labels permutation346 hz
    mixedMoment B raw7677step0 raw7677step0Labels = mixedMoment B raw7677step1 raw7677step1Labels := by
      have hz : ∀ j, raw7677step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7677step1 = (fun i j => raw7677step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7677step1 raw7677step0; decide +kernel
      have hl : raw7677step1Labels = raw7677step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7677step0 raw7677step0Labels permutation56 hz
    mixedMoment B raw7677step1 raw7677step1Labels = mixedMoment B raw7677step2 raw7677step2Labels := by
      have ha : raw7677step2 = (fun i j => raw7677step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw7677step2 raw7677step1; decide +kernel
      have hl : raw7677step2Labels = raw7677step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7677step1 raw7677step1Labels permutation8 permutation7
    mixedMoment B raw7677step2 raw7677step2Labels = mixedMoment B raw7677step3 raw7677step3Labels := by
      have ha : raw7677step3 = raw7677step2 := by apply Matrix.ext; unfold raw7677step3 raw7677step2; decide +kernel
      have hl : raw7677step2Labels = labelEmbedding1 ∘ raw7677step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7677step2 raw7677step2Labels raw7677step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2765 node2765Labels := by rfl

def raw7678 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7678Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7678step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7678step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7678step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7678step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7678step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![-2, 0, 2]]
def raw7678step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7678step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![2, 0, -2]]
def raw7678step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7678step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![2, 0, -2]]
def raw7678step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7678 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7678 raw7678Labels = mixedMoment B node2786 node2786Labels := by
  calc
    mixedMoment B raw7678 raw7678Labels = mixedMoment B raw7678step0 raw7678step0Labels := by
      have hz : ∀ j, raw7678 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7678step0 = (fun i j => raw7678 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7678step0 raw7678; decide +kernel
      have hl : raw7678step0Labels = raw7678Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7678 raw7678Labels permutation434 hz
    mixedMoment B raw7678step0 raw7678step0Labels = mixedMoment B raw7678step1 raw7678step1Labels := by
      have hz : ∀ j, raw7678step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7678step1 = (fun i j => raw7678step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7678step1 raw7678step0; decide +kernel
      have hl : raw7678step1Labels = raw7678step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7678step0 raw7678step0Labels permutation80 hz
    mixedMoment B raw7678step1 raw7678step1Labels = mixedMoment B raw7678step2 raw7678step2Labels := by
      have hz : ∀ j, raw7678step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw7678step2 = (fun i j => raw7678step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw7678step2 raw7678step1; decide +kernel
      have hl : raw7678step2Labels = raw7678step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7678step1 raw7678step1Labels permutation14 hz
    mixedMoment B raw7678step2 raw7678step2Labels = mixedMoment B raw7678step3 raw7678step3Labels := by
      have ha : raw7678step3 = (fun i j => raw7678step2 (permutation2 i) (permutation7 j)) := by apply Matrix.ext; unfold raw7678step3 raw7678step2; decide +kernel
      have hl : raw7678step3Labels = raw7678step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7678step2 raw7678step2Labels permutation2 permutation7
    mixedMoment B raw7678step3 raw7678step3Labels = mixedMoment B raw7678step4 raw7678step4Labels := by
      have ha : raw7678step4 = raw7678step3 := by apply Matrix.ext; unfold raw7678step4 raw7678step3; decide +kernel
      have hl : raw7678step3Labels = labelEmbedding1 ∘ raw7678step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7678step3 raw7678step3Labels raw7678step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2786 node2786Labels := by rfl

def raw7679 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw7679Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7679step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw7679step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7679step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw7679step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7679step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-3, 1, 2]]
def raw7679step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7679step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![2, 1, -3]]
def raw7679step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7679step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![2, 1, -3]]
def raw7679step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7679 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7679 raw7679Labels = mixedMoment B node2783 node2783Labels := by
  calc
    mixedMoment B raw7679 raw7679Labels = mixedMoment B raw7679step0 raw7679step0Labels := by
      have hz : ∀ j, raw7679 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7679step0 = (fun i j => raw7679 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7679step0 raw7679; decide +kernel
      have hl : raw7679step0Labels = raw7679Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7679 raw7679Labels permutation434 hz
    mixedMoment B raw7679step0 raw7679step0Labels = mixedMoment B raw7679step1 raw7679step1Labels := by
      have hz : ∀ j, raw7679step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7679step1 = (fun i j => raw7679step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7679step1 raw7679step0; decide +kernel
      have hl : raw7679step1Labels = raw7679step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7679step0 raw7679step0Labels permutation80 hz
    mixedMoment B raw7679step1 raw7679step1Labels = mixedMoment B raw7679step2 raw7679step2Labels := by
      have hz : ∀ j, raw7679step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw7679step2 = (fun i j => raw7679step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw7679step2 raw7679step1; decide +kernel
      have hl : raw7679step2Labels = raw7679step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7679step1 raw7679step1Labels permutation14 hz
    mixedMoment B raw7679step2 raw7679step2Labels = mixedMoment B raw7679step3 raw7679step3Labels := by
      have ha : raw7679step3 = (fun i j => raw7679step2 (permutation2 i) (permutation7 j)) := by apply Matrix.ext; unfold raw7679step3 raw7679step2; decide +kernel
      have hl : raw7679step3Labels = raw7679step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7679step2 raw7679step2Labels permutation2 permutation7
    mixedMoment B raw7679step3 raw7679step3Labels = mixedMoment B raw7679step4 raw7679step4Labels := by
      have ha : raw7679step4 = raw7679step3 := by apply Matrix.ext; unfold raw7679step4 raw7679step3; decide +kernel
      have hl : raw7679step3Labels = labelEmbedding1 ∘ raw7679step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7679step3 raw7679step3Labels raw7679step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2783 node2783Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
