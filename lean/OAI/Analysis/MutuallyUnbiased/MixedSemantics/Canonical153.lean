import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes9
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes10
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes14
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes23
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes24
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes64
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes65
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes67
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes69

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw19584 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19584Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19584step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19584step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19584step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19584step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19584step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, -3, 4]]
def raw19584step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19584step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-4, 2, 2]]
def raw19584step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19584step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![4, -2, -2]]
def raw19584step4Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19584step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![4, -2, -2]]
def raw19584step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19584 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19584 raw19584Labels = mixedMoment B node4468 node4468Labels := by
  calc
    mixedMoment B raw19584 raw19584Labels = mixedMoment B raw19584step0 raw19584step0Labels := by
      have hz : ∀ j, raw19584 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19584step0 = (fun i j => raw19584 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19584step0 raw19584; decide +kernel
      have hl : raw19584step0Labels = raw19584Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19584 raw19584Labels permutation434 hz
    mixedMoment B raw19584step0 raw19584step0Labels = mixedMoment B raw19584step1 raw19584step1Labels := by
      have hz : ∀ j, raw19584step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19584step1 = (fun i j => raw19584step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19584step1 raw19584step0; decide +kernel
      have hl : raw19584step1Labels = raw19584step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19584step0 raw19584step0Labels permutation80 hz
    mixedMoment B raw19584step1 raw19584step1Labels = mixedMoment B raw19584step2 raw19584step2Labels := by
      have hz : ∀ j, raw19584step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19584step2 = (fun i j => raw19584step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19584step2 raw19584step1; decide +kernel
      have hl : raw19584step2Labels = raw19584step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19584step1 raw19584step1Labels permutation14 hz
    mixedMoment B raw19584step2 raw19584step2Labels = mixedMoment B raw19584step3 raw19584step3Labels := by
      have ha : raw19584step3 = (fun i j => raw19584step2 (permutation7 i) (permutation6 j)) := by apply Matrix.ext; unfold raw19584step3 raw19584step2; decide +kernel
      have hl : raw19584step3Labels = raw19584step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19584step2 raw19584step2Labels permutation7 permutation6
    mixedMoment B raw19584step3 raw19584step3Labels = mixedMoment B raw19584step4 raw19584step4Labels := by
      have ha : raw19584step4 = -raw19584step3 := by apply Matrix.ext; change ∀ i j, raw19584step4 i j = -(raw19584step3 i j); unfold raw19584step4 raw19584step3; decide +kernel
      have hl : raw19584step4Labels = raw19584step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19584step4 raw19584step4Labels = mixedMoment B raw19584step5 raw19584step5Labels := by
      have ha : raw19584step5 = raw19584step4 := by apply Matrix.ext; unfold raw19584step5 raw19584step4; decide +kernel
      have hl : raw19584step4Labels = labelEmbedding9 ∘ raw19584step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19584step4 raw19584step4Labels raw19584step5Labels labelEmbedding9 hl
    _ = mixedMoment B node4468 node4468Labels := by rfl

def raw19585 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-2, -2, 4]]
def raw19585Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19585step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![-2, -2, 4]]
def raw19585step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19585step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, 0, 0], ![-2, -2, 4]]
def raw19585step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19585step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-2, -2, 4]]
def raw19585step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19585step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, -2, -2], ![0, -1, 1], ![-4, 3, 1]]
def raw19585step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19585step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![4, -3, -1]]
def raw19585step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19585 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19585 raw19585Labels = mixedMoment B node1275 node1275Labels := by
  calc
    mixedMoment B raw19585 raw19585Labels = mixedMoment B raw19585step0 raw19585step0Labels := by
      have hz : ∀ j, raw19585 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19585step0 = (fun i j => raw19585 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19585step0 raw19585; decide +kernel
      have hl : raw19585step0Labels = raw19585Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19585 raw19585Labels permutation520 hz
    mixedMoment B raw19585step0 raw19585step0Labels = mixedMoment B raw19585step1 raw19585step1Labels := by
      have hz : ∀ j, raw19585step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw19585step1 = (fun i j => raw19585step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw19585step1 raw19585step0; decide +kernel
      have hl : raw19585step1Labels = raw19585step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19585step0 raw19585step0Labels permutation104 hz
    mixedMoment B raw19585step1 raw19585step1Labels = mixedMoment B raw19585step2 raw19585step2Labels := by
      have hz : ∀ j, raw19585step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw19585step2 = (fun i j => raw19585step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw19585step2 raw19585step1; decide +kernel
      have hl : raw19585step2Labels = raw19585step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19585step1 raw19585step1Labels permutation20 hz
    mixedMoment B raw19585step2 raw19585step2Labels = mixedMoment B raw19585step3 raw19585step3Labels := by
      have ha : raw19585step3 = (fun i j => raw19585step2 (permutation7 i) (permutation6 j)) := by apply Matrix.ext; unfold raw19585step3 raw19585step2; decide +kernel
      have hl : raw19585step3Labels = raw19585step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19585step2 raw19585step2Labels permutation7 permutation6
    mixedMoment B raw19585step3 raw19585step3Labels = mixedMoment B raw19585step4 raw19585step4Labels := by
      have ha : raw19585step4 = -raw19585step3 := by apply Matrix.ext; change ∀ i j, raw19585step4 i j = -(raw19585step3 i j); unfold raw19585step4 raw19585step3; decide +kernel
      have hl : raw19585step4Labels = raw19585step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1275 node1275Labels := by rfl

def raw19586 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![-2, -2, 4]]
def raw19586Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19586step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![-2, -2, 4]]
def raw19586step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19586step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 1, 0], ![-2, -2, 4]]
def raw19586step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19586step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-2, -2, 4]]
def raw19586step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19586step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, -2, -2], ![0, -1, 1], ![-4, 3, 1]]
def raw19586step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19586step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![4, -3, -1]]
def raw19586step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19586 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19586 raw19586Labels = mixedMoment B node1275 node1275Labels := by
  calc
    mixedMoment B raw19586 raw19586Labels = mixedMoment B raw19586step0 raw19586step0Labels := by
      have hz : ∀ j, raw19586 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19586step0 = (fun i j => raw19586 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19586step0 raw19586; decide +kernel
      have hl : raw19586step0Labels = raw19586Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19586 raw19586Labels permutation520 hz
    mixedMoment B raw19586step0 raw19586step0Labels = mixedMoment B raw19586step1 raw19586step1Labels := by
      have hz : ∀ j, raw19586step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw19586step1 = (fun i j => raw19586step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw19586step1 raw19586step0; decide +kernel
      have hl : raw19586step1Labels = raw19586step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19586step0 raw19586step0Labels permutation104 hz
    mixedMoment B raw19586step1 raw19586step1Labels = mixedMoment B raw19586step2 raw19586step2Labels := by
      have hz : ∀ j, raw19586step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19586step2 = (fun i j => raw19586step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19586step2 raw19586step1; decide +kernel
      have hl : raw19586step2Labels = raw19586step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19586step1 raw19586step1Labels permutation14 hz
    mixedMoment B raw19586step2 raw19586step2Labels = mixedMoment B raw19586step3 raw19586step3Labels := by
      have ha : raw19586step3 = (fun i j => raw19586step2 (permutation7 i) (permutation6 j)) := by apply Matrix.ext; unfold raw19586step3 raw19586step2; decide +kernel
      have hl : raw19586step3Labels = raw19586step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19586step2 raw19586step2Labels permutation7 permutation6
    mixedMoment B raw19586step3 raw19586step3Labels = mixedMoment B raw19586step4 raw19586step4Labels := by
      have ha : raw19586step4 = -raw19586step3 := by apply Matrix.ext; change ∀ i j, raw19586step4 i j = -(raw19586step3 i j); unfold raw19586step4 raw19586step3; decide +kernel
      have hl : raw19586step4Labels = raw19586step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1275 node1275Labels := by rfl

def raw19587 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![-2, -2, 4]]
def raw19587Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19587step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-2, -2, 4]]
def raw19587step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19587step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 1, 0], ![-2, -2, 4]]
def raw19587step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19587step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-2, -2, 4]]
def raw19587step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19587step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, -2, -2], ![0, -1, 1], ![-4, 3, 1]]
def raw19587step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19587step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![4, -3, -1]]
def raw19587step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19587 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19587 raw19587Labels = mixedMoment B node1275 node1275Labels := by
  calc
    mixedMoment B raw19587 raw19587Labels = mixedMoment B raw19587step0 raw19587step0Labels := by
      have hz : ∀ j, raw19587 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19587step0 = (fun i j => raw19587 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19587step0 raw19587; decide +kernel
      have hl : raw19587step0Labels = raw19587Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19587 raw19587Labels permutation520 hz
    mixedMoment B raw19587step0 raw19587step0Labels = mixedMoment B raw19587step1 raw19587step1Labels := by
      have hz : ∀ j, raw19587step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19587step1 = (fun i j => raw19587step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19587step1 raw19587step0; decide +kernel
      have hl : raw19587step1Labels = raw19587step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19587step0 raw19587step0Labels permutation80 hz
    mixedMoment B raw19587step1 raw19587step1Labels = mixedMoment B raw19587step2 raw19587step2Labels := by
      have hz : ∀ j, raw19587step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19587step2 = (fun i j => raw19587step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19587step2 raw19587step1; decide +kernel
      have hl : raw19587step2Labels = raw19587step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19587step1 raw19587step1Labels permutation14 hz
    mixedMoment B raw19587step2 raw19587step2Labels = mixedMoment B raw19587step3 raw19587step3Labels := by
      have ha : raw19587step3 = (fun i j => raw19587step2 (permutation7 i) (permutation6 j)) := by apply Matrix.ext; unfold raw19587step3 raw19587step2; decide +kernel
      have hl : raw19587step3Labels = raw19587step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19587step2 raw19587step2Labels permutation7 permutation6
    mixedMoment B raw19587step3 raw19587step3Labels = mixedMoment B raw19587step4 raw19587step4Labels := by
      have ha : raw19587step4 = -raw19587step3 := by apply Matrix.ext; change ∀ i j, raw19587step4 i j = -(raw19587step3 i j); unfold raw19587step4 raw19587step3; decide +kernel
      have hl : raw19587step4Labels = raw19587step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1275 node1275Labels := by rfl

def raw19588 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-2, -2, 4]]
def raw19588Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19588step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-2, -2, 4]]
def raw19588step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19588step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 1, 0], ![-2, -2, 4]]
def raw19588step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19588step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-2, -2, 4]]
def raw19588step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19588step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, -2, -2], ![0, -1, 1], ![-4, 3, 1]]
def raw19588step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19588step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![4, -3, -1]]
def raw19588step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19588 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19588 raw19588Labels = mixedMoment B node1275 node1275Labels := by
  calc
    mixedMoment B raw19588 raw19588Labels = mixedMoment B raw19588step0 raw19588step0Labels := by
      have hz : ∀ j, raw19588 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19588step0 = (fun i j => raw19588 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19588step0 raw19588; decide +kernel
      have hl : raw19588step0Labels = raw19588Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19588 raw19588Labels permutation434 hz
    mixedMoment B raw19588step0 raw19588step0Labels = mixedMoment B raw19588step1 raw19588step1Labels := by
      have hz : ∀ j, raw19588step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19588step1 = (fun i j => raw19588step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19588step1 raw19588step0; decide +kernel
      have hl : raw19588step1Labels = raw19588step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19588step0 raw19588step0Labels permutation80 hz
    mixedMoment B raw19588step1 raw19588step1Labels = mixedMoment B raw19588step2 raw19588step2Labels := by
      have hz : ∀ j, raw19588step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19588step2 = (fun i j => raw19588step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19588step2 raw19588step1; decide +kernel
      have hl : raw19588step2Labels = raw19588step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19588step1 raw19588step1Labels permutation14 hz
    mixedMoment B raw19588step2 raw19588step2Labels = mixedMoment B raw19588step3 raw19588step3Labels := by
      have ha : raw19588step3 = (fun i j => raw19588step2 (permutation7 i) (permutation6 j)) := by apply Matrix.ext; unfold raw19588step3 raw19588step2; decide +kernel
      have hl : raw19588step3Labels = raw19588step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19588step2 raw19588step2Labels permutation7 permutation6
    mixedMoment B raw19588step3 raw19588step3Labels = mixedMoment B raw19588step4 raw19588step4Labels := by
      have ha : raw19588step4 = -raw19588step3 := by apply Matrix.ext; change ∀ i j, raw19588step4 i j = -(raw19588step3 i j); unfold raw19588step4 raw19588step3; decide +kernel
      have hl : raw19588step4Labels = raw19588step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1275 node1275Labels := by rfl

def raw19589 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-3, -1, 4]]
def raw19589Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19589step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-3, -1, 4]]
def raw19589step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19589step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![-3, -1, 4]]
def raw19589step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19589step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-3, -1, 4]]
def raw19589step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19589step3 : Matrix (Fin 2) (Fin 3) ℤ := ![![3, 1, -4], ![-3, -1, 4]]
def raw19589step3Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19589step4 : Matrix (Fin 2) (Fin 3) ℤ := ![![-4, 3, 1], ![4, -3, -1]]
def raw19589step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19589 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19589 raw19589Labels = mixedMoment B node1456 node1456Labels := by
  calc
    mixedMoment B raw19589 raw19589Labels = mixedMoment B raw19589step0 raw19589step0Labels := by
      have hz : ∀ j, raw19589 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19589step0 = (fun i j => raw19589 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19589step0 raw19589; decide +kernel
      have hl : raw19589step0Labels = raw19589Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19589 raw19589Labels permutation520 hz
    mixedMoment B raw19589step0 raw19589step0Labels = mixedMoment B raw19589step1 raw19589step1Labels := by
      have hz : ∀ j, raw19589step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw19589step1 = (fun i j => raw19589step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw19589step1 raw19589step0; decide +kernel
      have hl : raw19589step1Labels = raw19589step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19589step0 raw19589step0Labels permutation104 hz
    mixedMoment B raw19589step1 raw19589step1Labels = mixedMoment B raw19589step2 raw19589step2Labels := by
      have hz : ∀ j, raw19589step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw19589step2 = (fun i j => raw19589step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw19589step2 raw19589step1; decide +kernel
      have hl : raw19589step2Labels = raw19589step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19589step1 raw19589step1Labels permutation20 hz
    mixedMoment B raw19589step2 raw19589step2Labels = mixedMoment B raw19589step3 raw19589step3Labels := by
      have hz : ∀ j, raw19589step2 (permutation4 0) j = 0 := by decide +kernel
      have ha : raw19589step3 = (fun i j => raw19589step2 (permutation4 i.succ) j) := by apply Matrix.ext; unfold raw19589step3 raw19589step2; decide +kernel
      have hl : raw19589step3Labels = raw19589step2Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19589step2 raw19589step2Labels permutation4 hz
    mixedMoment B raw19589step3 raw19589step3Labels = mixedMoment B raw19589step4 raw19589step4Labels := by
      have ha : raw19589step4 = (fun i j => raw19589step3 (permutation0 i) (permutation6 j)) := by apply Matrix.ext; unfold raw19589step4 raw19589step3; decide +kernel
      have hl : raw19589step4Labels = raw19589step3Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19589step3 raw19589step3Labels permutation0 permutation6
    _ = mixedMoment B node1456 node1456Labels := by rfl

def raw19590 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-2, -2, 4]]
def raw19590Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19590step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-2, -2, 4]]
def raw19590step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19590step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![-2, -2, 4]]
def raw19590step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19590step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-2, -2, 4]]
def raw19590step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19590step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![4, -2, -2]]
def raw19590step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19590 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19590 raw19590Labels = mixedMoment B node1051 node1051Labels := by
  calc
    mixedMoment B raw19590 raw19590Labels = mixedMoment B raw19590step0 raw19590step0Labels := by
      have hz : ∀ j, raw19590 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19590step0 = (fun i j => raw19590 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19590step0 raw19590; decide +kernel
      have hl : raw19590step0Labels = raw19590Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19590 raw19590Labels permutation520 hz
    mixedMoment B raw19590step0 raw19590step0Labels = mixedMoment B raw19590step1 raw19590step1Labels := by
      have hz : ∀ j, raw19590step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw19590step1 = (fun i j => raw19590step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw19590step1 raw19590step0; decide +kernel
      have hl : raw19590step1Labels = raw19590step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19590step0 raw19590step0Labels permutation104 hz
    mixedMoment B raw19590step1 raw19590step1Labels = mixedMoment B raw19590step2 raw19590step2Labels := by
      have hz : ∀ j, raw19590step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw19590step2 = (fun i j => raw19590step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw19590step2 raw19590step1; decide +kernel
      have hl : raw19590step2Labels = raw19590step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19590step1 raw19590step1Labels permutation20 hz
    mixedMoment B raw19590step2 raw19590step2Labels = mixedMoment B raw19590step3 raw19590step3Labels := by
      have ha : raw19590step3 = (fun i j => raw19590step2 (permutation2 i) (permutation6 j)) := by apply Matrix.ext; unfold raw19590step3 raw19590step2; decide +kernel
      have hl : raw19590step3Labels = raw19590step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19590step2 raw19590step2Labels permutation2 permutation6
    _ = mixedMoment B node1051 node1051Labels := by rfl

def raw19591 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![-2, -2, 4]]
def raw19591Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19591step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![-2, -2, 4]]
def raw19591step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19591step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![-2, -2, 4]]
def raw19591step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19591step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![4, -2, -2]]
def raw19591step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19591 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19591 raw19591Labels = mixedMoment B node1221 node1221Labels := by
  calc
    mixedMoment B raw19591 raw19591Labels = mixedMoment B raw19591step0 raw19591step0Labels := by
      have hz : ∀ j, raw19591 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19591step0 = (fun i j => raw19591 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19591step0 raw19591; decide +kernel
      have hl : raw19591step0Labels = raw19591Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19591 raw19591Labels permutation520 hz
    mixedMoment B raw19591step0 raw19591step0Labels = mixedMoment B raw19591step1 raw19591step1Labels := by
      have hz : ∀ j, raw19591step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw19591step1 = (fun i j => raw19591step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw19591step1 raw19591step0; decide +kernel
      have hl : raw19591step1Labels = raw19591step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19591step0 raw19591step0Labels permutation104 hz
    mixedMoment B raw19591step1 raw19591step1Labels = mixedMoment B raw19591step2 raw19591step2Labels := by
      have ha : raw19591step2 = (fun i j => raw19591step1 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw19591step2 raw19591step1; decide +kernel
      have hl : raw19591step2Labels = raw19591step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19591step1 raw19591step1Labels permutation10 permutation6
    _ = mixedMoment B node1221 node1221Labels := by rfl

def raw19592 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![-2, -2, 4]]
def raw19592Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19592step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-2, -2, 4]]
def raw19592step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19592step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![-2, -2, 4]]
def raw19592step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19592step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![4, -2, -2]]
def raw19592step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19592 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19592 raw19592Labels = mixedMoment B node1221 node1221Labels := by
  calc
    mixedMoment B raw19592 raw19592Labels = mixedMoment B raw19592step0 raw19592step0Labels := by
      have hz : ∀ j, raw19592 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19592step0 = (fun i j => raw19592 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19592step0 raw19592; decide +kernel
      have hl : raw19592step0Labels = raw19592Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19592 raw19592Labels permutation520 hz
    mixedMoment B raw19592step0 raw19592step0Labels = mixedMoment B raw19592step1 raw19592step1Labels := by
      have hz : ∀ j, raw19592step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19592step1 = (fun i j => raw19592step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19592step1 raw19592step0; decide +kernel
      have hl : raw19592step1Labels = raw19592step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19592step0 raw19592step0Labels permutation80 hz
    mixedMoment B raw19592step1 raw19592step1Labels = mixedMoment B raw19592step2 raw19592step2Labels := by
      have ha : raw19592step2 = (fun i j => raw19592step1 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw19592step2 raw19592step1; decide +kernel
      have hl : raw19592step2Labels = raw19592step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19592step1 raw19592step1Labels permutation10 permutation6
    _ = mixedMoment B node1221 node1221Labels := by rfl

def raw19593 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-2, -2, 4]]
def raw19593Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19593step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-2, -2, 4]]
def raw19593step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19593step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![-2, -2, 4]]
def raw19593step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19593step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![4, -2, -2]]
def raw19593step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19593 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19593 raw19593Labels = mixedMoment B node1221 node1221Labels := by
  calc
    mixedMoment B raw19593 raw19593Labels = mixedMoment B raw19593step0 raw19593step0Labels := by
      have hz : ∀ j, raw19593 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19593step0 = (fun i j => raw19593 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19593step0 raw19593; decide +kernel
      have hl : raw19593step0Labels = raw19593Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19593 raw19593Labels permutation434 hz
    mixedMoment B raw19593step0 raw19593step0Labels = mixedMoment B raw19593step1 raw19593step1Labels := by
      have hz : ∀ j, raw19593step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19593step1 = (fun i j => raw19593step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19593step1 raw19593step0; decide +kernel
      have hl : raw19593step1Labels = raw19593step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19593step0 raw19593step0Labels permutation80 hz
    mixedMoment B raw19593step1 raw19593step1Labels = mixedMoment B raw19593step2 raw19593step2Labels := by
      have ha : raw19593step2 = (fun i j => raw19593step1 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw19593step2 raw19593step1; decide +kernel
      have hl : raw19593step2Labels = raw19593step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19593step1 raw19593step1Labels permutation10 permutation6
    _ = mixedMoment B node1221 node1221Labels := by rfl

def raw19594 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-3, -1, 4]]
def raw19594Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19594step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-3, -1, 4]]
def raw19594step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19594step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![-3, -1, 4]]
def raw19594step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19594step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-3, -1, 4]]
def raw19594step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19594step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![4, -3, -1]]
def raw19594step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19594 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19594 raw19594Labels = mixedMoment B node1275 node1275Labels := by
  calc
    mixedMoment B raw19594 raw19594Labels = mixedMoment B raw19594step0 raw19594step0Labels := by
      have hz : ∀ j, raw19594 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19594step0 = (fun i j => raw19594 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19594step0 raw19594; decide +kernel
      have hl : raw19594step0Labels = raw19594Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19594 raw19594Labels permutation520 hz
    mixedMoment B raw19594step0 raw19594step0Labels = mixedMoment B raw19594step1 raw19594step1Labels := by
      have hz : ∀ j, raw19594step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw19594step1 = (fun i j => raw19594step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw19594step1 raw19594step0; decide +kernel
      have hl : raw19594step1Labels = raw19594step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19594step0 raw19594step0Labels permutation104 hz
    mixedMoment B raw19594step1 raw19594step1Labels = mixedMoment B raw19594step2 raw19594step2Labels := by
      have hz : ∀ j, raw19594step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw19594step2 = (fun i j => raw19594step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw19594step2 raw19594step1; decide +kernel
      have hl : raw19594step2Labels = raw19594step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19594step1 raw19594step1Labels permutation20 hz
    mixedMoment B raw19594step2 raw19594step2Labels = mixedMoment B raw19594step3 raw19594step3Labels := by
      have ha : raw19594step3 = (fun i j => raw19594step2 (permutation2 i) (permutation6 j)) := by apply Matrix.ext; unfold raw19594step3 raw19594step2; decide +kernel
      have hl : raw19594step3Labels = raw19594step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19594step2 raw19594step2Labels permutation2 permutation6
    _ = mixedMoment B node1275 node1275Labels := by rfl

def raw19595 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-2, -2, 4]]
def raw19595Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19595step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-2, -2, 4]]
def raw19595step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19595step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![-2, -2, 4]]
def raw19595step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19595step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-2, -2, 4]]
def raw19595step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19595step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![4, -2, -2]]
def raw19595step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19595 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19595 raw19595Labels = mixedMoment B node1051 node1051Labels := by
  calc
    mixedMoment B raw19595 raw19595Labels = mixedMoment B raw19595step0 raw19595step0Labels := by
      have hz : ∀ j, raw19595 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19595step0 = (fun i j => raw19595 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19595step0 raw19595; decide +kernel
      have hl : raw19595step0Labels = raw19595Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19595 raw19595Labels permutation520 hz
    mixedMoment B raw19595step0 raw19595step0Labels = mixedMoment B raw19595step1 raw19595step1Labels := by
      have hz : ∀ j, raw19595step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw19595step1 = (fun i j => raw19595step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw19595step1 raw19595step0; decide +kernel
      have hl : raw19595step1Labels = raw19595step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19595step0 raw19595step0Labels permutation104 hz
    mixedMoment B raw19595step1 raw19595step1Labels = mixedMoment B raw19595step2 raw19595step2Labels := by
      have hz : ∀ j, raw19595step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19595step2 = (fun i j => raw19595step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19595step2 raw19595step1; decide +kernel
      have hl : raw19595step2Labels = raw19595step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19595step1 raw19595step1Labels permutation14 hz
    mixedMoment B raw19595step2 raw19595step2Labels = mixedMoment B raw19595step3 raw19595step3Labels := by
      have ha : raw19595step3 = (fun i j => raw19595step2 (permutation2 i) (permutation6 j)) := by apply Matrix.ext; unfold raw19595step3 raw19595step2; decide +kernel
      have hl : raw19595step3Labels = raw19595step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19595step2 raw19595step2Labels permutation2 permutation6
    _ = mixedMoment B node1051 node1051Labels := by rfl

def raw19596 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-2, -2, 4]]
def raw19596Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19596step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![-2, -2, 4]]
def raw19596step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19596step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![-2, -2, 4]]
def raw19596step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19596step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![4, -2, -2]]
def raw19596step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19596 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19596 raw19596Labels = mixedMoment B node1221 node1221Labels := by
  calc
    mixedMoment B raw19596 raw19596Labels = mixedMoment B raw19596step0 raw19596step0Labels := by
      have hz : ∀ j, raw19596 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19596step0 = (fun i j => raw19596 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19596step0 raw19596; decide +kernel
      have hl : raw19596step0Labels = raw19596Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19596 raw19596Labels permutation520 hz
    mixedMoment B raw19596step0 raw19596step0Labels = mixedMoment B raw19596step1 raw19596step1Labels := by
      have hz : ∀ j, raw19596step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw19596step1 = (fun i j => raw19596step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw19596step1 raw19596step0; decide +kernel
      have hl : raw19596step1Labels = raw19596step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19596step0 raw19596step0Labels permutation104 hz
    mixedMoment B raw19596step1 raw19596step1Labels = mixedMoment B raw19596step2 raw19596step2Labels := by
      have ha : raw19596step2 = (fun i j => raw19596step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw19596step2 raw19596step1; decide +kernel
      have hl : raw19596step2Labels = raw19596step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19596step1 raw19596step1Labels permutation8 permutation6
    _ = mixedMoment B node1221 node1221Labels := by rfl

def raw19597 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![-2, -2, 4]]
def raw19597Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19597step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![-2, -2, 4]]
def raw19597step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19597step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![-2, -2, 4]]
def raw19597step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19597step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![4, -2, -2]]
def raw19597step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19597 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19597 raw19597Labels = mixedMoment B node1221 node1221Labels := by
  calc
    mixedMoment B raw19597 raw19597Labels = mixedMoment B raw19597step0 raw19597step0Labels := by
      have hz : ∀ j, raw19597 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19597step0 = (fun i j => raw19597 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19597step0 raw19597; decide +kernel
      have hl : raw19597step0Labels = raw19597Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19597 raw19597Labels permutation520 hz
    mixedMoment B raw19597step0 raw19597step0Labels = mixedMoment B raw19597step1 raw19597step1Labels := by
      have hz : ∀ j, raw19597step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19597step1 = (fun i j => raw19597step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19597step1 raw19597step0; decide +kernel
      have hl : raw19597step1Labels = raw19597step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19597step0 raw19597step0Labels permutation56 hz
    mixedMoment B raw19597step1 raw19597step1Labels = mixedMoment B raw19597step2 raw19597step2Labels := by
      have ha : raw19597step2 = (fun i j => raw19597step1 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw19597step2 raw19597step1; decide +kernel
      have hl : raw19597step2Labels = raw19597step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19597step1 raw19597step1Labels permutation10 permutation6
    _ = mixedMoment B node1221 node1221Labels := by rfl

def raw19598 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-2, -2, 4]]
def raw19598Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19598step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![-2, -2, 4]]
def raw19598step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19598step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![-2, -2, 4]]
def raw19598step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19598step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![4, -2, -2]]
def raw19598step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19598 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19598 raw19598Labels = mixedMoment B node1221 node1221Labels := by
  calc
    mixedMoment B raw19598 raw19598Labels = mixedMoment B raw19598step0 raw19598step0Labels := by
      have hz : ∀ j, raw19598 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19598step0 = (fun i j => raw19598 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19598step0 raw19598; decide +kernel
      have hl : raw19598step0Labels = raw19598Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19598 raw19598Labels permutation434 hz
    mixedMoment B raw19598step0 raw19598step0Labels = mixedMoment B raw19598step1 raw19598step1Labels := by
      have hz : ∀ j, raw19598step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19598step1 = (fun i j => raw19598step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19598step1 raw19598step0; decide +kernel
      have hl : raw19598step1Labels = raw19598step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19598step0 raw19598step0Labels permutation56 hz
    mixedMoment B raw19598step1 raw19598step1Labels = mixedMoment B raw19598step2 raw19598step2Labels := by
      have ha : raw19598step2 = (fun i j => raw19598step1 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw19598step2 raw19598step1; decide +kernel
      have hl : raw19598step2Labels = raw19598step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19598step1 raw19598step1Labels permutation10 permutation6
    _ = mixedMoment B node1221 node1221Labels := by rfl

def raw19599 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-3, -1, 4]]
def raw19599Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19599step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-3, -1, 4]]
def raw19599step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19599step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-3, -1, 4]]
def raw19599step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19599step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-3, -1, 4]]
def raw19599step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19599step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![4, -3, -1]]
def raw19599step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19599 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19599 raw19599Labels = mixedMoment B node1275 node1275Labels := by
  calc
    mixedMoment B raw19599 raw19599Labels = mixedMoment B raw19599step0 raw19599step0Labels := by
      have hz : ∀ j, raw19599 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19599step0 = (fun i j => raw19599 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19599step0 raw19599; decide +kernel
      have hl : raw19599step0Labels = raw19599Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19599 raw19599Labels permutation520 hz
    mixedMoment B raw19599step0 raw19599step0Labels = mixedMoment B raw19599step1 raw19599step1Labels := by
      have hz : ∀ j, raw19599step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw19599step1 = (fun i j => raw19599step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw19599step1 raw19599step0; decide +kernel
      have hl : raw19599step1Labels = raw19599step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19599step0 raw19599step0Labels permutation104 hz
    mixedMoment B raw19599step1 raw19599step1Labels = mixedMoment B raw19599step2 raw19599step2Labels := by
      have hz : ∀ j, raw19599step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19599step2 = (fun i j => raw19599step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19599step2 raw19599step1; decide +kernel
      have hl : raw19599step2Labels = raw19599step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19599step1 raw19599step1Labels permutation14 hz
    mixedMoment B raw19599step2 raw19599step2Labels = mixedMoment B raw19599step3 raw19599step3Labels := by
      have ha : raw19599step3 = (fun i j => raw19599step2 (permutation2 i) (permutation6 j)) := by apply Matrix.ext; unfold raw19599step3 raw19599step2; decide +kernel
      have hl : raw19599step3Labels = raw19599step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19599step2 raw19599step2Labels permutation2 permutation6
    _ = mixedMoment B node1275 node1275Labels := by rfl

def raw19600 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-2, -2, 4]]
def raw19600Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19600step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-2, -2, 4]]
def raw19600step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19600step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![-2, -2, 4]]
def raw19600step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19600step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-2, -2, 4]]
def raw19600step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19600step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![4, -2, -2]]
def raw19600step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19600 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19600 raw19600Labels = mixedMoment B node1051 node1051Labels := by
  calc
    mixedMoment B raw19600 raw19600Labels = mixedMoment B raw19600step0 raw19600step0Labels := by
      have hz : ∀ j, raw19600 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19600step0 = (fun i j => raw19600 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19600step0 raw19600; decide +kernel
      have hl : raw19600step0Labels = raw19600Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19600 raw19600Labels permutation520 hz
    mixedMoment B raw19600step0 raw19600step0Labels = mixedMoment B raw19600step1 raw19600step1Labels := by
      have hz : ∀ j, raw19600step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19600step1 = (fun i j => raw19600step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19600step1 raw19600step0; decide +kernel
      have hl : raw19600step1Labels = raw19600step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19600step0 raw19600step0Labels permutation80 hz
    mixedMoment B raw19600step1 raw19600step1Labels = mixedMoment B raw19600step2 raw19600step2Labels := by
      have hz : ∀ j, raw19600step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19600step2 = (fun i j => raw19600step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19600step2 raw19600step1; decide +kernel
      have hl : raw19600step2Labels = raw19600step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19600step1 raw19600step1Labels permutation14 hz
    mixedMoment B raw19600step2 raw19600step2Labels = mixedMoment B raw19600step3 raw19600step3Labels := by
      have ha : raw19600step3 = (fun i j => raw19600step2 (permutation2 i) (permutation6 j)) := by apply Matrix.ext; unfold raw19600step3 raw19600step2; decide +kernel
      have hl : raw19600step3Labels = raw19600step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19600step2 raw19600step2Labels permutation2 permutation6
    _ = mixedMoment B node1051 node1051Labels := by rfl

def raw19601 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-2, -2, 4]]
def raw19601Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19601step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![-2, -2, 4]]
def raw19601step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19601step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![-2, -2, 4]]
def raw19601step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19601step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![4, -2, -2]]
def raw19601step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19601 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19601 raw19601Labels = mixedMoment B node1221 node1221Labels := by
  calc
    mixedMoment B raw19601 raw19601Labels = mixedMoment B raw19601step0 raw19601step0Labels := by
      have hz : ∀ j, raw19601 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19601step0 = (fun i j => raw19601 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19601step0 raw19601; decide +kernel
      have hl : raw19601step0Labels = raw19601Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19601 raw19601Labels permutation520 hz
    mixedMoment B raw19601step0 raw19601step0Labels = mixedMoment B raw19601step1 raw19601step1Labels := by
      have hz : ∀ j, raw19601step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19601step1 = (fun i j => raw19601step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19601step1 raw19601step0; decide +kernel
      have hl : raw19601step1Labels = raw19601step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19601step0 raw19601step0Labels permutation80 hz
    mixedMoment B raw19601step1 raw19601step1Labels = mixedMoment B raw19601step2 raw19601step2Labels := by
      have ha : raw19601step2 = (fun i j => raw19601step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw19601step2 raw19601step1; decide +kernel
      have hl : raw19601step2Labels = raw19601step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19601step1 raw19601step1Labels permutation8 permutation6
    _ = mixedMoment B node1221 node1221Labels := by rfl

def raw19602 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![-2, -2, 4]]
def raw19602Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19602step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![-2, -2, 4]]
def raw19602step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19602step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![-2, -2, 4]]
def raw19602step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19602step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![4, -2, -2]]
def raw19602step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19602 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19602 raw19602Labels = mixedMoment B node1221 node1221Labels := by
  calc
    mixedMoment B raw19602 raw19602Labels = mixedMoment B raw19602step0 raw19602step0Labels := by
      have hz : ∀ j, raw19602 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19602step0 = (fun i j => raw19602 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19602step0 raw19602; decide +kernel
      have hl : raw19602step0Labels = raw19602Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19602 raw19602Labels permutation520 hz
    mixedMoment B raw19602step0 raw19602step0Labels = mixedMoment B raw19602step1 raw19602step1Labels := by
      have hz : ∀ j, raw19602step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19602step1 = (fun i j => raw19602step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19602step1 raw19602step0; decide +kernel
      have hl : raw19602step1Labels = raw19602step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19602step0 raw19602step0Labels permutation56 hz
    mixedMoment B raw19602step1 raw19602step1Labels = mixedMoment B raw19602step2 raw19602step2Labels := by
      have ha : raw19602step2 = (fun i j => raw19602step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw19602step2 raw19602step1; decide +kernel
      have hl : raw19602step2Labels = raw19602step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19602step1 raw19602step1Labels permutation8 permutation6
    _ = mixedMoment B node1221 node1221Labels := by rfl

def raw19603 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![-2, -2, 4]]
def raw19603Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19603step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![-2, -2, 4]]
def raw19603step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19603step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![-2, -2, 4]]
def raw19603step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19603step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![4, -2, -2]]
def raw19603step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19603 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19603 raw19603Labels = mixedMoment B node1221 node1221Labels := by
  calc
    mixedMoment B raw19603 raw19603Labels = mixedMoment B raw19603step0 raw19603step0Labels := by
      have hz : ∀ j, raw19603 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19603step0 = (fun i j => raw19603 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19603step0 raw19603; decide +kernel
      have hl : raw19603step0Labels = raw19603Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19603 raw19603Labels permutation346 hz
    mixedMoment B raw19603step0 raw19603step0Labels = mixedMoment B raw19603step1 raw19603step1Labels := by
      have hz : ∀ j, raw19603step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19603step1 = (fun i j => raw19603step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19603step1 raw19603step0; decide +kernel
      have hl : raw19603step1Labels = raw19603step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19603step0 raw19603step0Labels permutation56 hz
    mixedMoment B raw19603step1 raw19603step1Labels = mixedMoment B raw19603step2 raw19603step2Labels := by
      have ha : raw19603step2 = (fun i j => raw19603step1 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw19603step2 raw19603step1; decide +kernel
      have hl : raw19603step2Labels = raw19603step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19603step1 raw19603step1Labels permutation10 permutation6
    _ = mixedMoment B node1221 node1221Labels := by rfl

def raw19604 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-3, -1, 4]]
def raw19604Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19604step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-3, -1, 4]]
def raw19604step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19604step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-3, -1, 4]]
def raw19604step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19604step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-3, -1, 4]]
def raw19604step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19604step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![4, -3, -1]]
def raw19604step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19604 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19604 raw19604Labels = mixedMoment B node1275 node1275Labels := by
  calc
    mixedMoment B raw19604 raw19604Labels = mixedMoment B raw19604step0 raw19604step0Labels := by
      have hz : ∀ j, raw19604 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19604step0 = (fun i j => raw19604 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19604step0 raw19604; decide +kernel
      have hl : raw19604step0Labels = raw19604Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19604 raw19604Labels permutation520 hz
    mixedMoment B raw19604step0 raw19604step0Labels = mixedMoment B raw19604step1 raw19604step1Labels := by
      have hz : ∀ j, raw19604step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19604step1 = (fun i j => raw19604step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19604step1 raw19604step0; decide +kernel
      have hl : raw19604step1Labels = raw19604step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19604step0 raw19604step0Labels permutation80 hz
    mixedMoment B raw19604step1 raw19604step1Labels = mixedMoment B raw19604step2 raw19604step2Labels := by
      have hz : ∀ j, raw19604step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19604step2 = (fun i j => raw19604step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19604step2 raw19604step1; decide +kernel
      have hl : raw19604step2Labels = raw19604step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19604step1 raw19604step1Labels permutation14 hz
    mixedMoment B raw19604step2 raw19604step2Labels = mixedMoment B raw19604step3 raw19604step3Labels := by
      have ha : raw19604step3 = (fun i j => raw19604step2 (permutation2 i) (permutation6 j)) := by apply Matrix.ext; unfold raw19604step3 raw19604step2; decide +kernel
      have hl : raw19604step3Labels = raw19604step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19604step2 raw19604step2Labels permutation2 permutation6
    _ = mixedMoment B node1275 node1275Labels := by rfl

def raw19605 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-2, -2, 4]]
def raw19605Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19605step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-2, -2, 4]]
def raw19605step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19605step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![-2, -2, 4]]
def raw19605step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19605step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-2, -2, 4]]
def raw19605step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19605step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![4, -2, -2]]
def raw19605step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19605 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19605 raw19605Labels = mixedMoment B node1051 node1051Labels := by
  calc
    mixedMoment B raw19605 raw19605Labels = mixedMoment B raw19605step0 raw19605step0Labels := by
      have hz : ∀ j, raw19605 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19605step0 = (fun i j => raw19605 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19605step0 raw19605; decide +kernel
      have hl : raw19605step0Labels = raw19605Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19605 raw19605Labels permutation434 hz
    mixedMoment B raw19605step0 raw19605step0Labels = mixedMoment B raw19605step1 raw19605step1Labels := by
      have hz : ∀ j, raw19605step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19605step1 = (fun i j => raw19605step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19605step1 raw19605step0; decide +kernel
      have hl : raw19605step1Labels = raw19605step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19605step0 raw19605step0Labels permutation80 hz
    mixedMoment B raw19605step1 raw19605step1Labels = mixedMoment B raw19605step2 raw19605step2Labels := by
      have hz : ∀ j, raw19605step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19605step2 = (fun i j => raw19605step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19605step2 raw19605step1; decide +kernel
      have hl : raw19605step2Labels = raw19605step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19605step1 raw19605step1Labels permutation14 hz
    mixedMoment B raw19605step2 raw19605step2Labels = mixedMoment B raw19605step3 raw19605step3Labels := by
      have ha : raw19605step3 = (fun i j => raw19605step2 (permutation2 i) (permutation6 j)) := by apply Matrix.ext; unfold raw19605step3 raw19605step2; decide +kernel
      have hl : raw19605step3Labels = raw19605step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19605step2 raw19605step2Labels permutation2 permutation6
    _ = mixedMoment B node1051 node1051Labels := by rfl

def raw19606 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-2, -2, 4]]
def raw19606Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19606step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![-2, -2, 4]]
def raw19606step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19606step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![-2, -2, 4]]
def raw19606step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19606step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![4, -2, -2]]
def raw19606step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19606 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19606 raw19606Labels = mixedMoment B node1221 node1221Labels := by
  calc
    mixedMoment B raw19606 raw19606Labels = mixedMoment B raw19606step0 raw19606step0Labels := by
      have hz : ∀ j, raw19606 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19606step0 = (fun i j => raw19606 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19606step0 raw19606; decide +kernel
      have hl : raw19606step0Labels = raw19606Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19606 raw19606Labels permutation434 hz
    mixedMoment B raw19606step0 raw19606step0Labels = mixedMoment B raw19606step1 raw19606step1Labels := by
      have hz : ∀ j, raw19606step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19606step1 = (fun i j => raw19606step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19606step1 raw19606step0; decide +kernel
      have hl : raw19606step1Labels = raw19606step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19606step0 raw19606step0Labels permutation80 hz
    mixedMoment B raw19606step1 raw19606step1Labels = mixedMoment B raw19606step2 raw19606step2Labels := by
      have ha : raw19606step2 = (fun i j => raw19606step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw19606step2 raw19606step1; decide +kernel
      have hl : raw19606step2Labels = raw19606step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19606step1 raw19606step1Labels permutation8 permutation6
    _ = mixedMoment B node1221 node1221Labels := by rfl

def raw19607 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![-2, -2, 4]]
def raw19607Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19607step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![-2, -2, 4]]
def raw19607step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19607step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![-2, -2, 4]]
def raw19607step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19607step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![4, -2, -2]]
def raw19607step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19607 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19607 raw19607Labels = mixedMoment B node1221 node1221Labels := by
  calc
    mixedMoment B raw19607 raw19607Labels = mixedMoment B raw19607step0 raw19607step0Labels := by
      have hz : ∀ j, raw19607 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19607step0 = (fun i j => raw19607 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19607step0 raw19607; decide +kernel
      have hl : raw19607step0Labels = raw19607Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19607 raw19607Labels permutation434 hz
    mixedMoment B raw19607step0 raw19607step0Labels = mixedMoment B raw19607step1 raw19607step1Labels := by
      have hz : ∀ j, raw19607step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19607step1 = (fun i j => raw19607step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19607step1 raw19607step0; decide +kernel
      have hl : raw19607step1Labels = raw19607step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19607step0 raw19607step0Labels permutation56 hz
    mixedMoment B raw19607step1 raw19607step1Labels = mixedMoment B raw19607step2 raw19607step2Labels := by
      have ha : raw19607step2 = (fun i j => raw19607step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw19607step2 raw19607step1; decide +kernel
      have hl : raw19607step2Labels = raw19607step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19607step1 raw19607step1Labels permutation8 permutation6
    _ = mixedMoment B node1221 node1221Labels := by rfl

def raw19608 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![-2, -2, 4]]
def raw19608Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19608step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![-2, -2, 4]]
def raw19608step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19608step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![-2, -2, 4]]
def raw19608step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19608step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![4, -2, -2]]
def raw19608step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19608 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19608 raw19608Labels = mixedMoment B node1221 node1221Labels := by
  calc
    mixedMoment B raw19608 raw19608Labels = mixedMoment B raw19608step0 raw19608step0Labels := by
      have hz : ∀ j, raw19608 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19608step0 = (fun i j => raw19608 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19608step0 raw19608; decide +kernel
      have hl : raw19608step0Labels = raw19608Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19608 raw19608Labels permutation346 hz
    mixedMoment B raw19608step0 raw19608step0Labels = mixedMoment B raw19608step1 raw19608step1Labels := by
      have hz : ∀ j, raw19608step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19608step1 = (fun i j => raw19608step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19608step1 raw19608step0; decide +kernel
      have hl : raw19608step1Labels = raw19608step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19608step0 raw19608step0Labels permutation56 hz
    mixedMoment B raw19608step1 raw19608step1Labels = mixedMoment B raw19608step2 raw19608step2Labels := by
      have ha : raw19608step2 = (fun i j => raw19608step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw19608step2 raw19608step1; decide +kernel
      have hl : raw19608step2Labels = raw19608step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19608step1 raw19608step1Labels permutation8 permutation6
    _ = mixedMoment B node1221 node1221Labels := by rfl

def raw19609 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-3, -1, 4]]
def raw19609Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19609step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-3, -1, 4]]
def raw19609step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19609step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-3, -1, 4]]
def raw19609step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19609step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-3, -1, 4]]
def raw19609step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19609step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![4, -3, -1]]
def raw19609step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19609 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19609 raw19609Labels = mixedMoment B node1275 node1275Labels := by
  calc
    mixedMoment B raw19609 raw19609Labels = mixedMoment B raw19609step0 raw19609step0Labels := by
      have hz : ∀ j, raw19609 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19609step0 = (fun i j => raw19609 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19609step0 raw19609; decide +kernel
      have hl : raw19609step0Labels = raw19609Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19609 raw19609Labels permutation434 hz
    mixedMoment B raw19609step0 raw19609step0Labels = mixedMoment B raw19609step1 raw19609step1Labels := by
      have hz : ∀ j, raw19609step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19609step1 = (fun i j => raw19609step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19609step1 raw19609step0; decide +kernel
      have hl : raw19609step1Labels = raw19609step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19609step0 raw19609step0Labels permutation80 hz
    mixedMoment B raw19609step1 raw19609step1Labels = mixedMoment B raw19609step2 raw19609step2Labels := by
      have hz : ∀ j, raw19609step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19609step2 = (fun i j => raw19609step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19609step2 raw19609step1; decide +kernel
      have hl : raw19609step2Labels = raw19609step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19609step1 raw19609step1Labels permutation14 hz
    mixedMoment B raw19609step2 raw19609step2Labels = mixedMoment B raw19609step3 raw19609step3Labels := by
      have ha : raw19609step3 = (fun i j => raw19609step2 (permutation2 i) (permutation6 j)) := by apply Matrix.ext; unfold raw19609step3 raw19609step2; decide +kernel
      have hl : raw19609step3Labels = raw19609step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19609step2 raw19609step2Labels permutation2 permutation6
    _ = mixedMoment B node1275 node1275Labels := by rfl

def raw19610 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -3, 4]]
def raw19610Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19610step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -3, 4]]
def raw19610step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19610step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![-1, -3, 4]]
def raw19610step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19610step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, -3, 4]]
def raw19610step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19610step3 : Matrix (Fin 2) (Fin 3) ℤ := ![![1, 3, -4], ![-1, -3, 4]]
def raw19610step3Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19610step4 : Matrix (Fin 2) (Fin 3) ℤ := ![![-4, 1, 3], ![4, -1, -3]]
def raw19610step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19610 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19610 raw19610Labels = mixedMoment B node1096 node1096Labels := by
  calc
    mixedMoment B raw19610 raw19610Labels = mixedMoment B raw19610step0 raw19610step0Labels := by
      have hz : ∀ j, raw19610 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19610step0 = (fun i j => raw19610 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19610step0 raw19610; decide +kernel
      have hl : raw19610step0Labels = raw19610Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19610 raw19610Labels permutation520 hz
    mixedMoment B raw19610step0 raw19610step0Labels = mixedMoment B raw19610step1 raw19610step1Labels := by
      have hz : ∀ j, raw19610step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw19610step1 = (fun i j => raw19610step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw19610step1 raw19610step0; decide +kernel
      have hl : raw19610step1Labels = raw19610step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19610step0 raw19610step0Labels permutation104 hz
    mixedMoment B raw19610step1 raw19610step1Labels = mixedMoment B raw19610step2 raw19610step2Labels := by
      have hz : ∀ j, raw19610step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw19610step2 = (fun i j => raw19610step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw19610step2 raw19610step1; decide +kernel
      have hl : raw19610step2Labels = raw19610step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19610step1 raw19610step1Labels permutation20 hz
    mixedMoment B raw19610step2 raw19610step2Labels = mixedMoment B raw19610step3 raw19610step3Labels := by
      have hz : ∀ j, raw19610step2 (permutation4 0) j = 0 := by decide +kernel
      have ha : raw19610step3 = (fun i j => raw19610step2 (permutation4 i.succ) j) := by apply Matrix.ext; unfold raw19610step3 raw19610step2; decide +kernel
      have hl : raw19610step3Labels = raw19610step2Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19610step2 raw19610step2Labels permutation4 hz
    mixedMoment B raw19610step3 raw19610step3Labels = mixedMoment B raw19610step4 raw19610step4Labels := by
      have ha : raw19610step4 = (fun i j => raw19610step3 (permutation0 i) (permutation6 j)) := by apply Matrix.ext; unfold raw19610step4 raw19610step3; decide +kernel
      have hl : raw19610step4Labels = raw19610step3Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19610step3 raw19610step3Labels permutation0 permutation6
    _ = mixedMoment B node1096 node1096Labels := by rfl

def raw19611 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -3, 4]]
def raw19611Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19611step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -3, 4]]
def raw19611step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19611step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![-1, -3, 4]]
def raw19611step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19611step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, -3, 4]]
def raw19611step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19611step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-4, 2, 2]]
def raw19611step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19611step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![4, -2, -2]]
def raw19611step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19611 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19611 raw19611Labels = mixedMoment B node1051 node1051Labels := by
  calc
    mixedMoment B raw19611 raw19611Labels = mixedMoment B raw19611step0 raw19611step0Labels := by
      have hz : ∀ j, raw19611 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19611step0 = (fun i j => raw19611 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19611step0 raw19611; decide +kernel
      have hl : raw19611step0Labels = raw19611Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19611 raw19611Labels permutation520 hz
    mixedMoment B raw19611step0 raw19611step0Labels = mixedMoment B raw19611step1 raw19611step1Labels := by
      have hz : ∀ j, raw19611step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw19611step1 = (fun i j => raw19611step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw19611step1 raw19611step0; decide +kernel
      have hl : raw19611step1Labels = raw19611step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19611step0 raw19611step0Labels permutation104 hz
    mixedMoment B raw19611step1 raw19611step1Labels = mixedMoment B raw19611step2 raw19611step2Labels := by
      have hz : ∀ j, raw19611step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw19611step2 = (fun i j => raw19611step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw19611step2 raw19611step1; decide +kernel
      have hl : raw19611step2Labels = raw19611step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19611step1 raw19611step1Labels permutation20 hz
    mixedMoment B raw19611step2 raw19611step2Labels = mixedMoment B raw19611step3 raw19611step3Labels := by
      have ha : raw19611step3 = (fun i j => raw19611step2 (permutation7 i) (permutation6 j)) := by apply Matrix.ext; unfold raw19611step3 raw19611step2; decide +kernel
      have hl : raw19611step3Labels = raw19611step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19611step2 raw19611step2Labels permutation7 permutation6
    mixedMoment B raw19611step3 raw19611step3Labels = mixedMoment B raw19611step4 raw19611step4Labels := by
      have ha : raw19611step4 = -raw19611step3 := by apply Matrix.ext; change ∀ i j, raw19611step4 i j = -(raw19611step3 i j); unfold raw19611step4 raw19611step3; decide +kernel
      have hl : raw19611step4Labels = raw19611step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1051 node1051Labels := by rfl

def raw19612 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -3, 4]]
def raw19612Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19612step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, -3, 4]]
def raw19612step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19612step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19612step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19612step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, -3, 4]]
def raw19612step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19612step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-4, 2, 2]]
def raw19612step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19612step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![4, -2, -2]]
def raw19612step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19612 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19612 raw19612Labels = mixedMoment B node1051 node1051Labels := by
  calc
    mixedMoment B raw19612 raw19612Labels = mixedMoment B raw19612step0 raw19612step0Labels := by
      have hz : ∀ j, raw19612 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19612step0 = (fun i j => raw19612 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19612step0 raw19612; decide +kernel
      have hl : raw19612step0Labels = raw19612Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19612 raw19612Labels permutation520 hz
    mixedMoment B raw19612step0 raw19612step0Labels = mixedMoment B raw19612step1 raw19612step1Labels := by
      have hz : ∀ j, raw19612step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw19612step1 = (fun i j => raw19612step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw19612step1 raw19612step0; decide +kernel
      have hl : raw19612step1Labels = raw19612step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19612step0 raw19612step0Labels permutation104 hz
    mixedMoment B raw19612step1 raw19612step1Labels = mixedMoment B raw19612step2 raw19612step2Labels := by
      have hz : ∀ j, raw19612step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19612step2 = (fun i j => raw19612step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19612step2 raw19612step1; decide +kernel
      have hl : raw19612step2Labels = raw19612step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19612step1 raw19612step1Labels permutation14 hz
    mixedMoment B raw19612step2 raw19612step2Labels = mixedMoment B raw19612step3 raw19612step3Labels := by
      have ha : raw19612step3 = (fun i j => raw19612step2 (permutation7 i) (permutation6 j)) := by apply Matrix.ext; unfold raw19612step3 raw19612step2; decide +kernel
      have hl : raw19612step3Labels = raw19612step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19612step2 raw19612step2Labels permutation7 permutation6
    mixedMoment B raw19612step3 raw19612step3Labels = mixedMoment B raw19612step4 raw19612step4Labels := by
      have ha : raw19612step4 = -raw19612step3 := by apply Matrix.ext; change ∀ i j, raw19612step4 i j = -(raw19612step3 i j); unfold raw19612step4 raw19612step3; decide +kernel
      have hl : raw19612step4Labels = raw19612step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1051 node1051Labels := by rfl

def raw19613 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, -3, 4]]
def raw19613Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19613step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19613step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19613step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19613step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19613step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, -3, 4]]
def raw19613step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19613step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-4, 2, 2]]
def raw19613step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19613step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![4, -2, -2]]
def raw19613step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19613 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19613 raw19613Labels = mixedMoment B node1051 node1051Labels := by
  calc
    mixedMoment B raw19613 raw19613Labels = mixedMoment B raw19613step0 raw19613step0Labels := by
      have hz : ∀ j, raw19613 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19613step0 = (fun i j => raw19613 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19613step0 raw19613; decide +kernel
      have hl : raw19613step0Labels = raw19613Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19613 raw19613Labels permutation520 hz
    mixedMoment B raw19613step0 raw19613step0Labels = mixedMoment B raw19613step1 raw19613step1Labels := by
      have hz : ∀ j, raw19613step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19613step1 = (fun i j => raw19613step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19613step1 raw19613step0; decide +kernel
      have hl : raw19613step1Labels = raw19613step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19613step0 raw19613step0Labels permutation80 hz
    mixedMoment B raw19613step1 raw19613step1Labels = mixedMoment B raw19613step2 raw19613step2Labels := by
      have hz : ∀ j, raw19613step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19613step2 = (fun i j => raw19613step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19613step2 raw19613step1; decide +kernel
      have hl : raw19613step2Labels = raw19613step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19613step1 raw19613step1Labels permutation14 hz
    mixedMoment B raw19613step2 raw19613step2Labels = mixedMoment B raw19613step3 raw19613step3Labels := by
      have ha : raw19613step3 = (fun i j => raw19613step2 (permutation7 i) (permutation6 j)) := by apply Matrix.ext; unfold raw19613step3 raw19613step2; decide +kernel
      have hl : raw19613step3Labels = raw19613step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19613step2 raw19613step2Labels permutation7 permutation6
    mixedMoment B raw19613step3 raw19613step3Labels = mixedMoment B raw19613step4 raw19613step4Labels := by
      have ha : raw19613step4 = -raw19613step3 := by apply Matrix.ext; change ∀ i j, raw19613step4 i j = -(raw19613step3 i j); unfold raw19613step4 raw19613step3; decide +kernel
      have hl : raw19613step4Labels = raw19613step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1051 node1051Labels := by rfl

def raw19614 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19614Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19614step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19614step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19614step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19614step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19614step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, -3, 4]]
def raw19614step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19614step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-4, 2, 2]]
def raw19614step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19614step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![4, -2, -2]]
def raw19614step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19614 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19614 raw19614Labels = mixedMoment B node1051 node1051Labels := by
  calc
    mixedMoment B raw19614 raw19614Labels = mixedMoment B raw19614step0 raw19614step0Labels := by
      have hz : ∀ j, raw19614 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19614step0 = (fun i j => raw19614 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19614step0 raw19614; decide +kernel
      have hl : raw19614step0Labels = raw19614Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19614 raw19614Labels permutation434 hz
    mixedMoment B raw19614step0 raw19614step0Labels = mixedMoment B raw19614step1 raw19614step1Labels := by
      have hz : ∀ j, raw19614step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19614step1 = (fun i j => raw19614step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19614step1 raw19614step0; decide +kernel
      have hl : raw19614step1Labels = raw19614step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19614step0 raw19614step0Labels permutation80 hz
    mixedMoment B raw19614step1 raw19614step1Labels = mixedMoment B raw19614step2 raw19614step2Labels := by
      have hz : ∀ j, raw19614step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19614step2 = (fun i j => raw19614step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19614step2 raw19614step1; decide +kernel
      have hl : raw19614step2Labels = raw19614step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19614step1 raw19614step1Labels permutation14 hz
    mixedMoment B raw19614step2 raw19614step2Labels = mixedMoment B raw19614step3 raw19614step3Labels := by
      have ha : raw19614step3 = (fun i j => raw19614step2 (permutation7 i) (permutation6 j)) := by apply Matrix.ext; unfold raw19614step3 raw19614step2; decide +kernel
      have hl : raw19614step3Labels = raw19614step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19614step2 raw19614step2Labels permutation7 permutation6
    mixedMoment B raw19614step3 raw19614step3Labels = mixedMoment B raw19614step4 raw19614step4Labels := by
      have ha : raw19614step4 = -raw19614step3 := by apply Matrix.ext; change ∀ i j, raw19614step4 i j = -(raw19614step3 i j); unfold raw19614step4 raw19614step3; decide +kernel
      have hl : raw19614step4Labels = raw19614step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1051 node1051Labels := by rfl

def raw19615 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![-2, -2, 4]]
def raw19615Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19615step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![-2, -2, 4]]
def raw19615step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19615step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 1, 0], ![-2, -2, 4]]
def raw19615step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19615step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-2, -2, 4]]
def raw19615step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19615step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![2, 2, -4]]
def raw19615step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19615 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19615 raw19615Labels = mixedMoment B node1752 node1752Labels := by
  calc
    mixedMoment B raw19615 raw19615Labels = mixedMoment B raw19615step0 raw19615step0Labels := by
      have hz : ∀ j, raw19615 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19615step0 = (fun i j => raw19615 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19615step0 raw19615; decide +kernel
      have hl : raw19615step0Labels = raw19615Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19615 raw19615Labels permutation520 hz
    mixedMoment B raw19615step0 raw19615step0Labels = mixedMoment B raw19615step1 raw19615step1Labels := by
      have hz : ∀ j, raw19615step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw19615step1 = (fun i j => raw19615step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw19615step1 raw19615step0; decide +kernel
      have hl : raw19615step1Labels = raw19615step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19615step0 raw19615step0Labels permutation104 hz
    mixedMoment B raw19615step1 raw19615step1Labels = mixedMoment B raw19615step2 raw19615step2Labels := by
      have hz : ∀ j, raw19615step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19615step2 = (fun i j => raw19615step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19615step2 raw19615step1; decide +kernel
      have hl : raw19615step2Labels = raw19615step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19615step1 raw19615step1Labels permutation14 hz
    mixedMoment B raw19615step2 raw19615step2Labels = mixedMoment B raw19615step3 raw19615step3Labels := by
      have ha : raw19615step3 = -raw19615step2 := by apply Matrix.ext; change ∀ i j, raw19615step3 i j = -(raw19615step2 i j); unfold raw19615step3 raw19615step2; decide +kernel
      have hl : raw19615step3Labels = raw19615step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1752 node1752Labels := by rfl

def raw19616 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![-2, -2, 4]]
def raw19616Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19616step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-2, -2, 4]]
def raw19616step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19616step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 1, 0], ![-2, -2, 4]]
def raw19616step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19616step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-2, -2, 4]]
def raw19616step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19616step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![2, 2, -4]]
def raw19616step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19616 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19616 raw19616Labels = mixedMoment B node1752 node1752Labels := by
  calc
    mixedMoment B raw19616 raw19616Labels = mixedMoment B raw19616step0 raw19616step0Labels := by
      have hz : ∀ j, raw19616 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19616step0 = (fun i j => raw19616 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19616step0 raw19616; decide +kernel
      have hl : raw19616step0Labels = raw19616Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19616 raw19616Labels permutation520 hz
    mixedMoment B raw19616step0 raw19616step0Labels = mixedMoment B raw19616step1 raw19616step1Labels := by
      have hz : ∀ j, raw19616step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19616step1 = (fun i j => raw19616step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19616step1 raw19616step0; decide +kernel
      have hl : raw19616step1Labels = raw19616step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19616step0 raw19616step0Labels permutation80 hz
    mixedMoment B raw19616step1 raw19616step1Labels = mixedMoment B raw19616step2 raw19616step2Labels := by
      have hz : ∀ j, raw19616step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19616step2 = (fun i j => raw19616step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19616step2 raw19616step1; decide +kernel
      have hl : raw19616step2Labels = raw19616step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19616step1 raw19616step1Labels permutation14 hz
    mixedMoment B raw19616step2 raw19616step2Labels = mixedMoment B raw19616step3 raw19616step3Labels := by
      have ha : raw19616step3 = -raw19616step2 := by apply Matrix.ext; change ∀ i j, raw19616step3 i j = -(raw19616step2 i j); unfold raw19616step3 raw19616step2; decide +kernel
      have hl : raw19616step3Labels = raw19616step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1752 node1752Labels := by rfl

def raw19617 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-2, -2, 4]]
def raw19617Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19617step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-2, -2, 4]]
def raw19617step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19617step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 1, 0], ![-2, -2, 4]]
def raw19617step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19617step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-2, -2, 4]]
def raw19617step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19617step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![2, 2, -4]]
def raw19617step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19617 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19617 raw19617Labels = mixedMoment B node1752 node1752Labels := by
  calc
    mixedMoment B raw19617 raw19617Labels = mixedMoment B raw19617step0 raw19617step0Labels := by
      have hz : ∀ j, raw19617 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19617step0 = (fun i j => raw19617 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19617step0 raw19617; decide +kernel
      have hl : raw19617step0Labels = raw19617Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19617 raw19617Labels permutation434 hz
    mixedMoment B raw19617step0 raw19617step0Labels = mixedMoment B raw19617step1 raw19617step1Labels := by
      have hz : ∀ j, raw19617step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19617step1 = (fun i j => raw19617step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19617step1 raw19617step0; decide +kernel
      have hl : raw19617step1Labels = raw19617step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19617step0 raw19617step0Labels permutation80 hz
    mixedMoment B raw19617step1 raw19617step1Labels = mixedMoment B raw19617step2 raw19617step2Labels := by
      have hz : ∀ j, raw19617step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19617step2 = (fun i j => raw19617step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19617step2 raw19617step1; decide +kernel
      have hl : raw19617step2Labels = raw19617step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19617step1 raw19617step1Labels permutation14 hz
    mixedMoment B raw19617step2 raw19617step2Labels = mixedMoment B raw19617step3 raw19617step3Labels := by
      have ha : raw19617step3 = -raw19617step2 := by apply Matrix.ext; change ∀ i j, raw19617step3 i j = -(raw19617step2 i j); unfold raw19617step3 raw19617step2; decide +kernel
      have hl : raw19617step3Labels = raw19617step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1752 node1752Labels := by rfl

def raw19618 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-3, -1, 4]]
def raw19618Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19618step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-3, -1, 4]]
def raw19618step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19618step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![-3, -1, 4]]
def raw19618step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19618step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-3, -1, 4]]
def raw19618step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19618step3 : Matrix (Fin 2) (Fin 3) ℤ := ![![3, 1, -4], ![-3, -1, 4]]
def raw19618step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19618step4 : Matrix (Fin 2) (Fin 3) ℤ := ![![-3, -1, 4], ![3, 1, -4]]
def raw19618step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19618 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19618 raw19618Labels = mixedMoment B node1758 node1758Labels := by
  calc
    mixedMoment B raw19618 raw19618Labels = mixedMoment B raw19618step0 raw19618step0Labels := by
      have hz : ∀ j, raw19618 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19618step0 = (fun i j => raw19618 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19618step0 raw19618; decide +kernel
      have hl : raw19618step0Labels = raw19618Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19618 raw19618Labels permutation520 hz
    mixedMoment B raw19618step0 raw19618step0Labels = mixedMoment B raw19618step1 raw19618step1Labels := by
      have hz : ∀ j, raw19618step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw19618step1 = (fun i j => raw19618step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw19618step1 raw19618step0; decide +kernel
      have hl : raw19618step1Labels = raw19618step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19618step0 raw19618step0Labels permutation104 hz
    mixedMoment B raw19618step1 raw19618step1Labels = mixedMoment B raw19618step2 raw19618step2Labels := by
      have hz : ∀ j, raw19618step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw19618step2 = (fun i j => raw19618step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw19618step2 raw19618step1; decide +kernel
      have hl : raw19618step2Labels = raw19618step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19618step1 raw19618step1Labels permutation20 hz
    mixedMoment B raw19618step2 raw19618step2Labels = mixedMoment B raw19618step3 raw19618step3Labels := by
      have hz : ∀ j, raw19618step2 (permutation4 0) j = 0 := by decide +kernel
      have ha : raw19618step3 = (fun i j => raw19618step2 (permutation4 i.succ) j) := by apply Matrix.ext; unfold raw19618step3 raw19618step2; decide +kernel
      have hl : raw19618step3Labels = raw19618step2Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19618step2 raw19618step2Labels permutation4 hz
    mixedMoment B raw19618step3 raw19618step3Labels = mixedMoment B raw19618step4 raw19618step4Labels := by
      have ha : raw19618step4 = (fun i j => raw19618step3 (permutation1 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19618step4 raw19618step3; decide +kernel
      have hl : raw19618step4Labels = raw19618step3Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19618step3 raw19618step3Labels permutation1 permutation2
    _ = mixedMoment B node1758 node1758Labels := by rfl

def raw19619 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19619Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19619step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19619step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19619step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19619step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19619step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![4, -3, -1]]
def raw19619step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19619step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![4, -3, -1]]
def raw19619step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19619 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19619 raw19619Labels = mixedMoment B node4159 node4159Labels := by
  calc
    mixedMoment B raw19619 raw19619Labels = mixedMoment B raw19619step0 raw19619step0Labels := by
      have hz : ∀ j, raw19619 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19619step0 = (fun i j => raw19619 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19619step0 raw19619; decide +kernel
      have hl : raw19619step0Labels = raw19619Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19619 raw19619Labels permutation434 hz
    mixedMoment B raw19619step0 raw19619step0Labels = mixedMoment B raw19619step1 raw19619step1Labels := by
      have hz : ∀ j, raw19619step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19619step1 = (fun i j => raw19619step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19619step1 raw19619step0; decide +kernel
      have hl : raw19619step1Labels = raw19619step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19619step0 raw19619step0Labels permutation80 hz
    mixedMoment B raw19619step1 raw19619step1Labels = mixedMoment B raw19619step2 raw19619step2Labels := by
      have ha : raw19619step2 = (fun i j => raw19619step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19619step2 raw19619step1; decide +kernel
      have hl : raw19619step2Labels = raw19619step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19619step1 raw19619step1Labels permutation10 permutation3
    mixedMoment B raw19619step2 raw19619step2Labels = mixedMoment B raw19619step3 raw19619step3Labels := by
      have ha : raw19619step3 = raw19619step2 := by apply Matrix.ext; unfold raw19619step3 raw19619step2; decide +kernel
      have hl : raw19619step2Labels = labelEmbedding6 ∘ raw19619step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19619step2 raw19619step2Labels raw19619step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4159 node4159Labels := by rfl

def raw19620 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19620Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19620step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19620step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19620step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-4, 2, 2]]
def raw19620step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19620step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![4, -2, -2]]
def raw19620step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19620 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19620 raw19620Labels = mixedMoment B node4330 node4330Labels := by
  calc
    mixedMoment B raw19620 raw19620Labels = mixedMoment B raw19620step0 raw19620step0Labels := by
      have hz : ∀ j, raw19620 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19620step0 = (fun i j => raw19620 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19620step0 raw19620; decide +kernel
      have hl : raw19620step0Labels = raw19620Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19620 raw19620Labels permutation434 hz
    mixedMoment B raw19620step0 raw19620step0Labels = mixedMoment B raw19620step1 raw19620step1Labels := by
      have ha : raw19620step1 = (fun i j => raw19620step0 (permutation139 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19620step1 raw19620step0; decide +kernel
      have hl : raw19620step1Labels = raw19620step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19620step0 raw19620step0Labels permutation139 permutation2
    mixedMoment B raw19620step1 raw19620step1Labels = mixedMoment B raw19620step2 raw19620step2Labels := by
      have ha : raw19620step2 = -raw19620step1 := by apply Matrix.ext; change ∀ i j, raw19620step2 i j = -(raw19620step1 i j); unfold raw19620step2 raw19620step1; decide +kernel
      have hl : raw19620step2Labels = raw19620step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4330 node4330Labels := by rfl

def raw19621 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19621Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19621step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19621step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19621step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-4, 2, 2]]
def raw19621step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19621step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![4, -2, -2]]
def raw19621step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19621 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19621 raw19621Labels = mixedMoment B node4330 node4330Labels := by
  calc
    mixedMoment B raw19621 raw19621Labels = mixedMoment B raw19621step0 raw19621step0Labels := by
      have hz : ∀ j, raw19621 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19621step0 = (fun i j => raw19621 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19621step0 raw19621; decide +kernel
      have hl : raw19621step0Labels = raw19621Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19621 raw19621Labels permutation346 hz
    mixedMoment B raw19621step0 raw19621step0Labels = mixedMoment B raw19621step1 raw19621step1Labels := by
      have ha : raw19621step1 = (fun i j => raw19621step0 (permutation139 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19621step1 raw19621step0; decide +kernel
      have hl : raw19621step1Labels = raw19621step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19621step0 raw19621step0Labels permutation139 permutation2
    mixedMoment B raw19621step1 raw19621step1Labels = mixedMoment B raw19621step2 raw19621step2Labels := by
      have ha : raw19621step2 = -raw19621step1 := by apply Matrix.ext; change ∀ i j, raw19621step2 i j = -(raw19621step1 i j); unfold raw19621step2 raw19621step1; decide +kernel
      have hl : raw19621step2Labels = raw19621step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4330 node4330Labels := by rfl

def raw19622 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![4, -1, -3]]
def raw19622Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19622step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![4, -1, -3]]
def raw19622step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19622step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 0, 1], ![4, -1, -3]]
def raw19622step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19622step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![-1, 0, 1], ![-4, 2, 2]]
def raw19622step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19622step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![4, -2, -2]]
def raw19622step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19622 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19622 raw19622Labels = mixedMoment B node4356 node4356Labels := by
  calc
    mixedMoment B raw19622 raw19622Labels = mixedMoment B raw19622step0 raw19622step0Labels := by
      have hz : ∀ j, raw19622 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19622step0 = (fun i j => raw19622 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19622step0 raw19622; decide +kernel
      have hl : raw19622step0Labels = raw19622Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19622 raw19622Labels permutation434 hz
    mixedMoment B raw19622step0 raw19622step0Labels = mixedMoment B raw19622step1 raw19622step1Labels := by
      have hz : ∀ j, raw19622step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19622step1 = (fun i j => raw19622step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19622step1 raw19622step0; decide +kernel
      have hl : raw19622step1Labels = raw19622step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19622step0 raw19622step0Labels permutation80 hz
    mixedMoment B raw19622step1 raw19622step1Labels = mixedMoment B raw19622step2 raw19622step2Labels := by
      have ha : raw19622step2 = (fun i j => raw19622step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19622step2 raw19622step1; decide +kernel
      have hl : raw19622step2Labels = raw19622step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19622step1 raw19622step1Labels permutation29 permutation2
    mixedMoment B raw19622step2 raw19622step2Labels = mixedMoment B raw19622step3 raw19622step3Labels := by
      have ha : raw19622step3 = -raw19622step2 := by apply Matrix.ext; change ∀ i j, raw19622step3 i j = -(raw19622step2 i j); unfold raw19622step3 raw19622step2; decide +kernel
      have hl : raw19622step3Labels = raw19622step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4356 node4356Labels := by rfl

def raw19623 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19623Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19623step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19623step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19623step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19623step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19623step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![4, -3, -1]]
def raw19623step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19623step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![4, -3, -1]]
def raw19623step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19623 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19623 raw19623Labels = mixedMoment B node4159 node4159Labels := by
  calc
    mixedMoment B raw19623 raw19623Labels = mixedMoment B raw19623step0 raw19623step0Labels := by
      have hz : ∀ j, raw19623 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19623step0 = (fun i j => raw19623 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19623step0 raw19623; decide +kernel
      have hl : raw19623step0Labels = raw19623Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19623 raw19623Labels permutation434 hz
    mixedMoment B raw19623step0 raw19623step0Labels = mixedMoment B raw19623step1 raw19623step1Labels := by
      have hz : ∀ j, raw19623step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19623step1 = (fun i j => raw19623step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19623step1 raw19623step0; decide +kernel
      have hl : raw19623step1Labels = raw19623step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19623step0 raw19623step0Labels permutation56 hz
    mixedMoment B raw19623step1 raw19623step1Labels = mixedMoment B raw19623step2 raw19623step2Labels := by
      have ha : raw19623step2 = (fun i j => raw19623step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19623step2 raw19623step1; decide +kernel
      have hl : raw19623step2Labels = raw19623step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19623step1 raw19623step1Labels permutation10 permutation3
    mixedMoment B raw19623step2 raw19623step2Labels = mixedMoment B raw19623step3 raw19623step3Labels := by
      have ha : raw19623step3 = raw19623step2 := by apply Matrix.ext; unfold raw19623step3 raw19623step2; decide +kernel
      have hl : raw19623step2Labels = labelEmbedding6 ∘ raw19623step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19623step2 raw19623step2Labels raw19623step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4159 node4159Labels := by rfl

def raw19624 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19624Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19624step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19624step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19624step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-4, 2, 2]]
def raw19624step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19624step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![4, -2, -2]]
def raw19624step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19624 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19624 raw19624Labels = mixedMoment B node4330 node4330Labels := by
  calc
    mixedMoment B raw19624 raw19624Labels = mixedMoment B raw19624step0 raw19624step0Labels := by
      have hz : ∀ j, raw19624 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19624step0 = (fun i j => raw19624 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19624step0 raw19624; decide +kernel
      have hl : raw19624step0Labels = raw19624Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19624 raw19624Labels permutation434 hz
    mixedMoment B raw19624step0 raw19624step0Labels = mixedMoment B raw19624step1 raw19624step1Labels := by
      have ha : raw19624step1 = (fun i j => raw19624step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19624step1 raw19624step0; decide +kernel
      have hl : raw19624step1Labels = raw19624step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19624step0 raw19624step0Labels permutation145 permutation2
    mixedMoment B raw19624step1 raw19624step1Labels = mixedMoment B raw19624step2 raw19624step2Labels := by
      have ha : raw19624step2 = -raw19624step1 := by apply Matrix.ext; change ∀ i j, raw19624step2 i j = -(raw19624step1 i j); unfold raw19624step2 raw19624step1; decide +kernel
      have hl : raw19624step2Labels = raw19624step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4330 node4330Labels := by rfl

def raw19625 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19625Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19625step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19625step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19625step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-4, 2, 2]]
def raw19625step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19625step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![4, -2, -2]]
def raw19625step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19625 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19625 raw19625Labels = mixedMoment B node4330 node4330Labels := by
  calc
    mixedMoment B raw19625 raw19625Labels = mixedMoment B raw19625step0 raw19625step0Labels := by
      have hz : ∀ j, raw19625 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw19625step0 = (fun i j => raw19625 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw19625step0 raw19625; decide +kernel
      have hl : raw19625step0Labels = raw19625Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19625 raw19625Labels permutation265 hz
    mixedMoment B raw19625step0 raw19625step0Labels = mixedMoment B raw19625step1 raw19625step1Labels := by
      have ha : raw19625step1 = (fun i j => raw19625step0 (permutation139 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19625step1 raw19625step0; decide +kernel
      have hl : raw19625step1Labels = raw19625step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19625step0 raw19625step0Labels permutation139 permutation2
    mixedMoment B raw19625step1 raw19625step1Labels = mixedMoment B raw19625step2 raw19625step2Labels := by
      have ha : raw19625step2 = -raw19625step1 := by apply Matrix.ext; change ∀ i j, raw19625step2 i j = -(raw19625step1 i j); unfold raw19625step2 raw19625step1; decide +kernel
      have hl : raw19625step2Labels = raw19625step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4330 node4330Labels := by rfl

def raw19626 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![4, -1, -3]]
def raw19626Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19626step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![4, -1, -3]]
def raw19626step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19626step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 0, 1], ![4, -1, -3]]
def raw19626step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19626step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![-1, 0, 1], ![-4, 2, 2]]
def raw19626step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19626step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![4, -2, -2]]
def raw19626step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19626 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19626 raw19626Labels = mixedMoment B node4356 node4356Labels := by
  calc
    mixedMoment B raw19626 raw19626Labels = mixedMoment B raw19626step0 raw19626step0Labels := by
      have hz : ∀ j, raw19626 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19626step0 = (fun i j => raw19626 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19626step0 raw19626; decide +kernel
      have hl : raw19626step0Labels = raw19626Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19626 raw19626Labels permutation434 hz
    mixedMoment B raw19626step0 raw19626step0Labels = mixedMoment B raw19626step1 raw19626step1Labels := by
      have hz : ∀ j, raw19626step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19626step1 = (fun i j => raw19626step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19626step1 raw19626step0; decide +kernel
      have hl : raw19626step1Labels = raw19626step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19626step0 raw19626step0Labels permutation56 hz
    mixedMoment B raw19626step1 raw19626step1Labels = mixedMoment B raw19626step2 raw19626step2Labels := by
      have ha : raw19626step2 = (fun i j => raw19626step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19626step2 raw19626step1; decide +kernel
      have hl : raw19626step2Labels = raw19626step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19626step1 raw19626step1Labels permutation29 permutation2
    mixedMoment B raw19626step2 raw19626step2Labels = mixedMoment B raw19626step3 raw19626step3Labels := by
      have ha : raw19626step3 = -raw19626step2 := by apply Matrix.ext; change ∀ i j, raw19626step3 i j = -(raw19626step2 i j); unfold raw19626step3 raw19626step2; decide +kernel
      have hl : raw19626step3Labels = raw19626step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4356 node4356Labels := by rfl

def raw19627 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19627Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19627step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19627step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19627step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19627step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19627step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![4, -3, -1]]
def raw19627step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19627step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![4, -3, -1]]
def raw19627step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19627 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19627 raw19627Labels = mixedMoment B node4159 node4159Labels := by
  calc
    mixedMoment B raw19627 raw19627Labels = mixedMoment B raw19627step0 raw19627step0Labels := by
      have hz : ∀ j, raw19627 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19627step0 = (fun i j => raw19627 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19627step0 raw19627; decide +kernel
      have hl : raw19627step0Labels = raw19627Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19627 raw19627Labels permutation346 hz
    mixedMoment B raw19627step0 raw19627step0Labels = mixedMoment B raw19627step1 raw19627step1Labels := by
      have hz : ∀ j, raw19627step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19627step1 = (fun i j => raw19627step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19627step1 raw19627step0; decide +kernel
      have hl : raw19627step1Labels = raw19627step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19627step0 raw19627step0Labels permutation56 hz
    mixedMoment B raw19627step1 raw19627step1Labels = mixedMoment B raw19627step2 raw19627step2Labels := by
      have ha : raw19627step2 = (fun i j => raw19627step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19627step2 raw19627step1; decide +kernel
      have hl : raw19627step2Labels = raw19627step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19627step1 raw19627step1Labels permutation10 permutation3
    mixedMoment B raw19627step2 raw19627step2Labels = mixedMoment B raw19627step3 raw19627step3Labels := by
      have ha : raw19627step3 = raw19627step2 := by apply Matrix.ext; unfold raw19627step3 raw19627step2; decide +kernel
      have hl : raw19627step2Labels = labelEmbedding6 ∘ raw19627step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19627step2 raw19627step2Labels raw19627step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4159 node4159Labels := by rfl

def raw19628 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19628Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19628step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19628step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19628step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-4, 2, 2]]
def raw19628step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19628step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![4, -2, -2]]
def raw19628step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19628 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19628 raw19628Labels = mixedMoment B node4330 node4330Labels := by
  calc
    mixedMoment B raw19628 raw19628Labels = mixedMoment B raw19628step0 raw19628step0Labels := by
      have hz : ∀ j, raw19628 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19628step0 = (fun i j => raw19628 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19628step0 raw19628; decide +kernel
      have hl : raw19628step0Labels = raw19628Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19628 raw19628Labels permutation346 hz
    mixedMoment B raw19628step0 raw19628step0Labels = mixedMoment B raw19628step1 raw19628step1Labels := by
      have ha : raw19628step1 = (fun i j => raw19628step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19628step1 raw19628step0; decide +kernel
      have hl : raw19628step1Labels = raw19628step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19628step0 raw19628step0Labels permutation145 permutation2
    mixedMoment B raw19628step1 raw19628step1Labels = mixedMoment B raw19628step2 raw19628step2Labels := by
      have ha : raw19628step2 = -raw19628step1 := by apply Matrix.ext; change ∀ i j, raw19628step2 i j = -(raw19628step1 i j); unfold raw19628step2 raw19628step1; decide +kernel
      have hl : raw19628step2Labels = raw19628step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4330 node4330Labels := by rfl

def raw19629 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19629Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19629step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19629step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19629step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-4, 2, 2]]
def raw19629step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19629step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![4, -2, -2]]
def raw19629step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19629 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19629 raw19629Labels = mixedMoment B node4330 node4330Labels := by
  calc
    mixedMoment B raw19629 raw19629Labels = mixedMoment B raw19629step0 raw19629step0Labels := by
      have hz : ∀ j, raw19629 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw19629step0 = (fun i j => raw19629 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw19629step0 raw19629; decide +kernel
      have hl : raw19629step0Labels = raw19629Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19629 raw19629Labels permutation265 hz
    mixedMoment B raw19629step0 raw19629step0Labels = mixedMoment B raw19629step1 raw19629step1Labels := by
      have ha : raw19629step1 = (fun i j => raw19629step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19629step1 raw19629step0; decide +kernel
      have hl : raw19629step1Labels = raw19629step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19629step0 raw19629step0Labels permutation145 permutation2
    mixedMoment B raw19629step1 raw19629step1Labels = mixedMoment B raw19629step2 raw19629step2Labels := by
      have ha : raw19629step2 = -raw19629step1 := by apply Matrix.ext; change ∀ i j, raw19629step2 i j = -(raw19629step1 i j); unfold raw19629step2 raw19629step1; decide +kernel
      have hl : raw19629step2Labels = raw19629step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4330 node4330Labels := by rfl

def raw19630 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![4, -1, -3]]
def raw19630Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19630step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![4, -1, -3]]
def raw19630step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19630step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 0, 1], ![4, -1, -3]]
def raw19630step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19630step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![-1, 0, 1], ![-4, 2, 2]]
def raw19630step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19630step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![4, -2, -2]]
def raw19630step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19630 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19630 raw19630Labels = mixedMoment B node4356 node4356Labels := by
  calc
    mixedMoment B raw19630 raw19630Labels = mixedMoment B raw19630step0 raw19630step0Labels := by
      have hz : ∀ j, raw19630 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19630step0 = (fun i j => raw19630 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19630step0 raw19630; decide +kernel
      have hl : raw19630step0Labels = raw19630Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19630 raw19630Labels permutation346 hz
    mixedMoment B raw19630step0 raw19630step0Labels = mixedMoment B raw19630step1 raw19630step1Labels := by
      have hz : ∀ j, raw19630step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19630step1 = (fun i j => raw19630step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19630step1 raw19630step0; decide +kernel
      have hl : raw19630step1Labels = raw19630step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19630step0 raw19630step0Labels permutation56 hz
    mixedMoment B raw19630step1 raw19630step1Labels = mixedMoment B raw19630step2 raw19630step2Labels := by
      have ha : raw19630step2 = (fun i j => raw19630step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19630step2 raw19630step1; decide +kernel
      have hl : raw19630step2Labels = raw19630step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19630step1 raw19630step1Labels permutation29 permutation2
    mixedMoment B raw19630step2 raw19630step2Labels = mixedMoment B raw19630step3 raw19630step3Labels := by
      have ha : raw19630step3 = -raw19630step2 := by apply Matrix.ext; change ∀ i j, raw19630step3 i j = -(raw19630step2 i j); unfold raw19630step3 raw19630step2; decide +kernel
      have hl : raw19630step3Labels = raw19630step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4356 node4356Labels := by rfl

def raw19631 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![4, -1, -3]]
def raw19631Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19631step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![4, -1, -3]]
def raw19631step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19631step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -2, 1], ![4, -1, -3]]
def raw19631step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19631step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -2, 1], ![4, -1, -3]]
def raw19631step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19631step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 1, -2], ![4, -3, -1]]
def raw19631step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19631step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 1, -2], ![4, -3, -1]]
def raw19631step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19631 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19631 raw19631Labels = mixedMoment B node4189 node4189Labels := by
  calc
    mixedMoment B raw19631 raw19631Labels = mixedMoment B raw19631step0 raw19631step0Labels := by
      have hz : ∀ j, raw19631 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19631step0 = (fun i j => raw19631 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19631step0 raw19631; decide +kernel
      have hl : raw19631step0Labels = raw19631Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19631 raw19631Labels permutation434 hz
    mixedMoment B raw19631step0 raw19631step0Labels = mixedMoment B raw19631step1 raw19631step1Labels := by
      have hz : ∀ j, raw19631step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19631step1 = (fun i j => raw19631step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19631step1 raw19631step0; decide +kernel
      have hl : raw19631step1Labels = raw19631step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19631step0 raw19631step0Labels permutation80 hz
    mixedMoment B raw19631step1 raw19631step1Labels = mixedMoment B raw19631step2 raw19631step2Labels := by
      have hz : ∀ j, raw19631step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19631step2 = (fun i j => raw19631step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19631step2 raw19631step1; decide +kernel
      have hl : raw19631step2Labels = raw19631step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19631step1 raw19631step1Labels permutation14 hz
    mixedMoment B raw19631step2 raw19631step2Labels = mixedMoment B raw19631step3 raw19631step3Labels := by
      have ha : raw19631step3 = (fun i j => raw19631step2 (permutation2 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19631step3 raw19631step2; decide +kernel
      have hl : raw19631step3Labels = raw19631step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19631step2 raw19631step2Labels permutation2 permutation3
    mixedMoment B raw19631step3 raw19631step3Labels = mixedMoment B raw19631step4 raw19631step4Labels := by
      have ha : raw19631step4 = raw19631step3 := by apply Matrix.ext; unfold raw19631step4 raw19631step3; decide +kernel
      have hl : raw19631step3Labels = labelEmbedding6 ∘ raw19631step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19631step3 raw19631step3Labels raw19631step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4189 node4189Labels := by rfl

def raw19632 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![4, -1, -3]]
def raw19632Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19632step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![4, -1, -3]]
def raw19632step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19632step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -2, 1], ![4, -1, -3]]
def raw19632step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19632step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![1, -2, 1], ![-1, 1, 0], ![-4, 2, 2]]
def raw19632step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19632step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![4, -2, -2]]
def raw19632step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19632 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19632 raw19632Labels = mixedMoment B node4370 node4370Labels := by
  calc
    mixedMoment B raw19632 raw19632Labels = mixedMoment B raw19632step0 raw19632step0Labels := by
      have hz : ∀ j, raw19632 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19632step0 = (fun i j => raw19632 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19632step0 raw19632; decide +kernel
      have hl : raw19632step0Labels = raw19632Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19632 raw19632Labels permutation434 hz
    mixedMoment B raw19632step0 raw19632step0Labels = mixedMoment B raw19632step1 raw19632step1Labels := by
      have hz : ∀ j, raw19632step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19632step1 = (fun i j => raw19632step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19632step1 raw19632step0; decide +kernel
      have hl : raw19632step1Labels = raw19632step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19632step0 raw19632step0Labels permutation80 hz
    mixedMoment B raw19632step1 raw19632step1Labels = mixedMoment B raw19632step2 raw19632step2Labels := by
      have ha : raw19632step2 = (fun i j => raw19632step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19632step2 raw19632step1; decide +kernel
      have hl : raw19632step2Labels = raw19632step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19632step1 raw19632step1Labels permutation31 permutation2
    mixedMoment B raw19632step2 raw19632step2Labels = mixedMoment B raw19632step3 raw19632step3Labels := by
      have ha : raw19632step3 = -raw19632step2 := by apply Matrix.ext; change ∀ i j, raw19632step3 i j = -(raw19632step2 i j); unfold raw19632step3 raw19632step2; decide +kernel
      have hl : raw19632step3Labels = raw19632step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4370 node4370Labels := by rfl

def raw19633 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![4, -1, -3]]
def raw19633Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19633step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![4, -1, -3]]
def raw19633step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19633step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -2, 1], ![4, -1, -3]]
def raw19633step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19633step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![1, -2, 1], ![-1, 1, 0], ![-4, 2, 2]]
def raw19633step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19633step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![4, -2, -2]]
def raw19633step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19633 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19633 raw19633Labels = mixedMoment B node4370 node4370Labels := by
  calc
    mixedMoment B raw19633 raw19633Labels = mixedMoment B raw19633step0 raw19633step0Labels := by
      have hz : ∀ j, raw19633 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19633step0 = (fun i j => raw19633 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19633step0 raw19633; decide +kernel
      have hl : raw19633step0Labels = raw19633Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19633 raw19633Labels permutation434 hz
    mixedMoment B raw19633step0 raw19633step0Labels = mixedMoment B raw19633step1 raw19633step1Labels := by
      have hz : ∀ j, raw19633step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19633step1 = (fun i j => raw19633step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19633step1 raw19633step0; decide +kernel
      have hl : raw19633step1Labels = raw19633step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19633step0 raw19633step0Labels permutation56 hz
    mixedMoment B raw19633step1 raw19633step1Labels = mixedMoment B raw19633step2 raw19633step2Labels := by
      have ha : raw19633step2 = (fun i j => raw19633step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19633step2 raw19633step1; decide +kernel
      have hl : raw19633step2Labels = raw19633step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19633step1 raw19633step1Labels permutation31 permutation2
    mixedMoment B raw19633step2 raw19633step2Labels = mixedMoment B raw19633step3 raw19633step3Labels := by
      have ha : raw19633step3 = -raw19633step2 := by apply Matrix.ext; change ∀ i j, raw19633step3 i j = -(raw19633step2 i j); unfold raw19633step3 raw19633step2; decide +kernel
      have hl : raw19633step3Labels = raw19633step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4370 node4370Labels := by rfl

def raw19634 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![4, -1, -3]]
def raw19634Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19634step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![4, -1, -3]]
def raw19634step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19634step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -2, 1], ![4, -1, -3]]
def raw19634step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19634step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![1, -2, 1], ![-1, 1, 0], ![-4, 2, 2]]
def raw19634step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19634step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![4, -2, -2]]
def raw19634step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19634 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19634 raw19634Labels = mixedMoment B node4370 node4370Labels := by
  calc
    mixedMoment B raw19634 raw19634Labels = mixedMoment B raw19634step0 raw19634step0Labels := by
      have hz : ∀ j, raw19634 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19634step0 = (fun i j => raw19634 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19634step0 raw19634; decide +kernel
      have hl : raw19634step0Labels = raw19634Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19634 raw19634Labels permutation346 hz
    mixedMoment B raw19634step0 raw19634step0Labels = mixedMoment B raw19634step1 raw19634step1Labels := by
      have hz : ∀ j, raw19634step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19634step1 = (fun i j => raw19634step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19634step1 raw19634step0; decide +kernel
      have hl : raw19634step1Labels = raw19634step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19634step0 raw19634step0Labels permutation56 hz
    mixedMoment B raw19634step1 raw19634step1Labels = mixedMoment B raw19634step2 raw19634step2Labels := by
      have ha : raw19634step2 = (fun i j => raw19634step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19634step2 raw19634step1; decide +kernel
      have hl : raw19634step2Labels = raw19634step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19634step1 raw19634step1Labels permutation31 permutation2
    mixedMoment B raw19634step2 raw19634step2Labels = mixedMoment B raw19634step3 raw19634step3Labels := by
      have ha : raw19634step3 = -raw19634step2 := by apply Matrix.ext; change ∀ i j, raw19634step3 i j = -(raw19634step2 i j); unfold raw19634step3 raw19634step2; decide +kernel
      have hl : raw19634step3Labels = raw19634step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4370 node4370Labels := by rfl

def raw19635 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![5, -2, -3]]
def raw19635Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19635step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![5, -2, -3]]
def raw19635step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19635step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, -1, 1], ![5, -2, -3]]
def raw19635step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19635step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![5, -2, -3]]
def raw19635step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19635step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![5, -2, -3], ![0, -1, 1], ![-5, 3, 2]]
def raw19635step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19635step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![5, -3, -2]]
def raw19635step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19635 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19635 raw19635Labels = mixedMoment B node4163 node4163Labels := by
  calc
    mixedMoment B raw19635 raw19635Labels = mixedMoment B raw19635step0 raw19635step0Labels := by
      have hz : ∀ j, raw19635 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19635step0 = (fun i j => raw19635 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19635step0 raw19635; decide +kernel
      have hl : raw19635step0Labels = raw19635Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19635 raw19635Labels permutation434 hz
    mixedMoment B raw19635step0 raw19635step0Labels = mixedMoment B raw19635step1 raw19635step1Labels := by
      have hz : ∀ j, raw19635step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19635step1 = (fun i j => raw19635step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19635step1 raw19635step0; decide +kernel
      have hl : raw19635step1Labels = raw19635step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19635step0 raw19635step0Labels permutation80 hz
    mixedMoment B raw19635step1 raw19635step1Labels = mixedMoment B raw19635step2 raw19635step2Labels := by
      have hz : ∀ j, raw19635step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19635step2 = (fun i j => raw19635step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19635step2 raw19635step1; decide +kernel
      have hl : raw19635step2Labels = raw19635step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19635step1 raw19635step1Labels permutation14 hz
    mixedMoment B raw19635step2 raw19635step2Labels = mixedMoment B raw19635step3 raw19635step3Labels := by
      have ha : raw19635step3 = (fun i j => raw19635step2 (permutation7 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19635step3 raw19635step2; decide +kernel
      have hl : raw19635step3Labels = raw19635step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19635step2 raw19635step2Labels permutation7 permutation2
    mixedMoment B raw19635step3 raw19635step3Labels = mixedMoment B raw19635step4 raw19635step4Labels := by
      have ha : raw19635step4 = -raw19635step3 := by apply Matrix.ext; change ∀ i j, raw19635step4 i j = -(raw19635step3 i j); unfold raw19635step4 raw19635step3; decide +kernel
      have hl : raw19635step4Labels = raw19635step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4163 node4163Labels := by rfl

def raw19636 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![5, -2, -3]]
def raw19636Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19636step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![5, -2, -3]]
def raw19636step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19636step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![5, -2, -3]]
def raw19636step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19636step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![5, -2, -3], ![0, -1, 1], ![-1, 1, 0], ![-4, 2, 2]]
def raw19636step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19636step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![4, -2, -2]]
def raw19636step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19636 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19636 raw19636Labels = mixedMoment B node4156 node4156Labels := by
  calc
    mixedMoment B raw19636 raw19636Labels = mixedMoment B raw19636step0 raw19636step0Labels := by
      have hz : ∀ j, raw19636 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19636step0 = (fun i j => raw19636 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19636step0 raw19636; decide +kernel
      have hl : raw19636step0Labels = raw19636Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19636 raw19636Labels permutation434 hz
    mixedMoment B raw19636step0 raw19636step0Labels = mixedMoment B raw19636step1 raw19636step1Labels := by
      have hz : ∀ j, raw19636step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19636step1 = (fun i j => raw19636step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19636step1 raw19636step0; decide +kernel
      have hl : raw19636step1Labels = raw19636step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19636step0 raw19636step0Labels permutation80 hz
    mixedMoment B raw19636step1 raw19636step1Labels = mixedMoment B raw19636step2 raw19636step2Labels := by
      have ha : raw19636step2 = (fun i j => raw19636step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19636step2 raw19636step1; decide +kernel
      have hl : raw19636step2Labels = raw19636step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19636step1 raw19636step1Labels permutation31 permutation2
    mixedMoment B raw19636step2 raw19636step2Labels = mixedMoment B raw19636step3 raw19636step3Labels := by
      have ha : raw19636step3 = -raw19636step2 := by apply Matrix.ext; change ∀ i j, raw19636step3 i j = -(raw19636step2 i j); unfold raw19636step3 raw19636step2; decide +kernel
      have hl : raw19636step3Labels = raw19636step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4156 node4156Labels := by rfl

def raw19637 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![5, -2, -3]]
def raw19637Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19637step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![5, -2, -3]]
def raw19637step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19637step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![5, -2, -3]]
def raw19637step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19637step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![5, -2, -3], ![0, -1, 1], ![-1, 1, 0], ![-4, 2, 2]]
def raw19637step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19637step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![4, -2, -2]]
def raw19637step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19637 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19637 raw19637Labels = mixedMoment B node4156 node4156Labels := by
  calc
    mixedMoment B raw19637 raw19637Labels = mixedMoment B raw19637step0 raw19637step0Labels := by
      have hz : ∀ j, raw19637 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19637step0 = (fun i j => raw19637 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19637step0 raw19637; decide +kernel
      have hl : raw19637step0Labels = raw19637Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19637 raw19637Labels permutation434 hz
    mixedMoment B raw19637step0 raw19637step0Labels = mixedMoment B raw19637step1 raw19637step1Labels := by
      have hz : ∀ j, raw19637step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19637step1 = (fun i j => raw19637step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19637step1 raw19637step0; decide +kernel
      have hl : raw19637step1Labels = raw19637step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19637step0 raw19637step0Labels permutation56 hz
    mixedMoment B raw19637step1 raw19637step1Labels = mixedMoment B raw19637step2 raw19637step2Labels := by
      have ha : raw19637step2 = (fun i j => raw19637step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19637step2 raw19637step1; decide +kernel
      have hl : raw19637step2Labels = raw19637step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19637step1 raw19637step1Labels permutation31 permutation2
    mixedMoment B raw19637step2 raw19637step2Labels = mixedMoment B raw19637step3 raw19637step3Labels := by
      have ha : raw19637step3 = -raw19637step2 := by apply Matrix.ext; change ∀ i j, raw19637step3 i j = -(raw19637step2 i j); unfold raw19637step3 raw19637step2; decide +kernel
      have hl : raw19637step3Labels = raw19637step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4156 node4156Labels := by rfl

def raw19638 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![5, -2, -3]]
def raw19638Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19638step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![5, -2, -3]]
def raw19638step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19638step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![5, -2, -3]]
def raw19638step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19638step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![5, -2, -3], ![0, -1, 1], ![-1, 1, 0], ![-4, 2, 2]]
def raw19638step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19638step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![4, -2, -2]]
def raw19638step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19638 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19638 raw19638Labels = mixedMoment B node4156 node4156Labels := by
  calc
    mixedMoment B raw19638 raw19638Labels = mixedMoment B raw19638step0 raw19638step0Labels := by
      have hz : ∀ j, raw19638 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19638step0 = (fun i j => raw19638 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19638step0 raw19638; decide +kernel
      have hl : raw19638step0Labels = raw19638Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19638 raw19638Labels permutation346 hz
    mixedMoment B raw19638step0 raw19638step0Labels = mixedMoment B raw19638step1 raw19638step1Labels := by
      have hz : ∀ j, raw19638step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19638step1 = (fun i j => raw19638step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19638step1 raw19638step0; decide +kernel
      have hl : raw19638step1Labels = raw19638step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19638step0 raw19638step0Labels permutation56 hz
    mixedMoment B raw19638step1 raw19638step1Labels = mixedMoment B raw19638step2 raw19638step2Labels := by
      have ha : raw19638step2 = (fun i j => raw19638step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19638step2 raw19638step1; decide +kernel
      have hl : raw19638step2Labels = raw19638step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19638step1 raw19638step1Labels permutation31 permutation2
    mixedMoment B raw19638step2 raw19638step2Labels = mixedMoment B raw19638step3 raw19638step3Labels := by
      have ha : raw19638step3 = -raw19638step2 := by apply Matrix.ext; change ∀ i j, raw19638step3 i j = -(raw19638step2 i j); unfold raw19638step3 raw19638step2; decide +kernel
      have hl : raw19638step3Labels = raw19638step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4156 node4156Labels := by rfl

def raw19639 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![5, -2, -3]]
def raw19639Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19639step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![5, -2, -3]]
def raw19639step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19639step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 0, 1], ![5, -2, -3]]
def raw19639step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19639step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![5, -2, -3]]
def raw19639step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19639step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![5, -2, -3], ![-1, 0, 1], ![-4, 2, 2]]
def raw19639step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19639step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![4, -2, -2]]
def raw19639step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19639 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19639 raw19639Labels = mixedMoment B node4187 node4187Labels := by
  calc
    mixedMoment B raw19639 raw19639Labels = mixedMoment B raw19639step0 raw19639step0Labels := by
      have hz : ∀ j, raw19639 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19639step0 = (fun i j => raw19639 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19639step0 raw19639; decide +kernel
      have hl : raw19639step0Labels = raw19639Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19639 raw19639Labels permutation434 hz
    mixedMoment B raw19639step0 raw19639step0Labels = mixedMoment B raw19639step1 raw19639step1Labels := by
      have hz : ∀ j, raw19639step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19639step1 = (fun i j => raw19639step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19639step1 raw19639step0; decide +kernel
      have hl : raw19639step1Labels = raw19639step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19639step0 raw19639step0Labels permutation80 hz
    mixedMoment B raw19639step1 raw19639step1Labels = mixedMoment B raw19639step2 raw19639step2Labels := by
      have hz : ∀ j, raw19639step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19639step2 = (fun i j => raw19639step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19639step2 raw19639step1; decide +kernel
      have hl : raw19639step2Labels = raw19639step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19639step1 raw19639step1Labels permutation14 hz
    mixedMoment B raw19639step2 raw19639step2Labels = mixedMoment B raw19639step3 raw19639step3Labels := by
      have ha : raw19639step3 = (fun i j => raw19639step2 (permutation7 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19639step3 raw19639step2; decide +kernel
      have hl : raw19639step3Labels = raw19639step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19639step2 raw19639step2Labels permutation7 permutation2
    mixedMoment B raw19639step3 raw19639step3Labels = mixedMoment B raw19639step4 raw19639step4Labels := by
      have ha : raw19639step4 = -raw19639step3 := by apply Matrix.ext; change ∀ i j, raw19639step4 i j = -(raw19639step3 i j); unfold raw19639step4 raw19639step3; decide +kernel
      have hl : raw19639step4Labels = raw19639step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4187 node4187Labels := by rfl

def raw19640 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19640Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19640step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19640step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19640step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19640step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19640step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -3, -1], ![0, 1, -1], ![-1, 0, 1], ![-3, 2, 1]]
def raw19640step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19640step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw19640step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19640 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19640 raw19640Labels = mixedMoment B node1416 node1416Labels := by
  calc
    mixedMoment B raw19640 raw19640Labels = mixedMoment B raw19640step0 raw19640step0Labels := by
      have hz : ∀ j, raw19640 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19640step0 = (fun i j => raw19640 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19640step0 raw19640; decide +kernel
      have hl : raw19640step0Labels = raw19640Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19640 raw19640Labels permutation434 hz
    mixedMoment B raw19640step0 raw19640step0Labels = mixedMoment B raw19640step1 raw19640step1Labels := by
      have hz : ∀ j, raw19640step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19640step1 = (fun i j => raw19640step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19640step1 raw19640step0; decide +kernel
      have hl : raw19640step1Labels = raw19640step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19640step0 raw19640step0Labels permutation80 hz
    mixedMoment B raw19640step1 raw19640step1Labels = mixedMoment B raw19640step2 raw19640step2Labels := by
      have ha : raw19640step2 = (fun i j => raw19640step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19640step2 raw19640step1; decide +kernel
      have hl : raw19640step2Labels = raw19640step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19640step1 raw19640step1Labels permutation31 permutation3
    mixedMoment B raw19640step2 raw19640step2Labels = mixedMoment B raw19640step3 raw19640step3Labels := by
      have ha : raw19640step3 = -raw19640step2 := by apply Matrix.ext; change ∀ i j, raw19640step3 i j = -(raw19640step2 i j); unfold raw19640step3 raw19640step2; decide +kernel
      have hl : raw19640step3Labels = raw19640step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1416 node1416Labels := by rfl

def raw19641 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19641Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19641step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19641step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19641step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19641step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19641step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -3, -1], ![0, 1, -1], ![-1, 0, 1], ![-3, 2, 1]]
def raw19641step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19641step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw19641step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19641 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19641 raw19641Labels = mixedMoment B node1416 node1416Labels := by
  calc
    mixedMoment B raw19641 raw19641Labels = mixedMoment B raw19641step0 raw19641step0Labels := by
      have hz : ∀ j, raw19641 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19641step0 = (fun i j => raw19641 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19641step0 raw19641; decide +kernel
      have hl : raw19641step0Labels = raw19641Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19641 raw19641Labels permutation434 hz
    mixedMoment B raw19641step0 raw19641step0Labels = mixedMoment B raw19641step1 raw19641step1Labels := by
      have hz : ∀ j, raw19641step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19641step1 = (fun i j => raw19641step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19641step1 raw19641step0; decide +kernel
      have hl : raw19641step1Labels = raw19641step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19641step0 raw19641step0Labels permutation56 hz
    mixedMoment B raw19641step1 raw19641step1Labels = mixedMoment B raw19641step2 raw19641step2Labels := by
      have ha : raw19641step2 = (fun i j => raw19641step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19641step2 raw19641step1; decide +kernel
      have hl : raw19641step2Labels = raw19641step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19641step1 raw19641step1Labels permutation31 permutation3
    mixedMoment B raw19641step2 raw19641step2Labels = mixedMoment B raw19641step3 raw19641step3Labels := by
      have ha : raw19641step3 = -raw19641step2 := by apply Matrix.ext; change ∀ i j, raw19641step3 i j = -(raw19641step2 i j); unfold raw19641step3 raw19641step2; decide +kernel
      have hl : raw19641step3Labels = raw19641step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1416 node1416Labels := by rfl

def raw19642 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19642Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19642step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19642step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19642step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19642step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19642step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -3, -1], ![0, 1, -1], ![-1, 0, 1], ![-3, 2, 1]]
def raw19642step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19642step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw19642step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19642 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19642 raw19642Labels = mixedMoment B node1416 node1416Labels := by
  calc
    mixedMoment B raw19642 raw19642Labels = mixedMoment B raw19642step0 raw19642step0Labels := by
      have hz : ∀ j, raw19642 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19642step0 = (fun i j => raw19642 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19642step0 raw19642; decide +kernel
      have hl : raw19642step0Labels = raw19642Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19642 raw19642Labels permutation346 hz
    mixedMoment B raw19642step0 raw19642step0Labels = mixedMoment B raw19642step1 raw19642step1Labels := by
      have hz : ∀ j, raw19642step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19642step1 = (fun i j => raw19642step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19642step1 raw19642step0; decide +kernel
      have hl : raw19642step1Labels = raw19642step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19642step0 raw19642step0Labels permutation56 hz
    mixedMoment B raw19642step1 raw19642step1Labels = mixedMoment B raw19642step2 raw19642step2Labels := by
      have ha : raw19642step2 = (fun i j => raw19642step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19642step2 raw19642step1; decide +kernel
      have hl : raw19642step2Labels = raw19642step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19642step1 raw19642step1Labels permutation31 permutation3
    mixedMoment B raw19642step2 raw19642step2Labels = mixedMoment B raw19642step3 raw19642step3Labels := by
      have ha : raw19642step3 = -raw19642step2 := by apply Matrix.ext; change ∀ i j, raw19642step3 i j = -(raw19642step2 i j); unfold raw19642step3 raw19642step2; decide +kernel
      have hl : raw19642step3Labels = raw19642step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1416 node1416Labels := by rfl

def raw19643 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![4, -1, -3]]
def raw19643Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19643step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![4, -1, -3]]
def raw19643step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19643step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 0, 1], ![4, -1, -3]]
def raw19643step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19643step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![4, -1, -3]]
def raw19643step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19643step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, -3, -1], ![-1, 1, 0], ![-3, 2, 1]]
def raw19643step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19643step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![3, -2, -1]]
def raw19643step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19643 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19643 raw19643Labels = mixedMoment B node1450 node1450Labels := by
  calc
    mixedMoment B raw19643 raw19643Labels = mixedMoment B raw19643step0 raw19643step0Labels := by
      have hz : ∀ j, raw19643 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19643step0 = (fun i j => raw19643 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19643step0 raw19643; decide +kernel
      have hl : raw19643step0Labels = raw19643Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19643 raw19643Labels permutation434 hz
    mixedMoment B raw19643step0 raw19643step0Labels = mixedMoment B raw19643step1 raw19643step1Labels := by
      have hz : ∀ j, raw19643step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19643step1 = (fun i j => raw19643step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19643step1 raw19643step0; decide +kernel
      have hl : raw19643step1Labels = raw19643step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19643step0 raw19643step0Labels permutation80 hz
    mixedMoment B raw19643step1 raw19643step1Labels = mixedMoment B raw19643step2 raw19643step2Labels := by
      have hz : ∀ j, raw19643step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19643step2 = (fun i j => raw19643step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19643step2 raw19643step1; decide +kernel
      have hl : raw19643step2Labels = raw19643step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19643step1 raw19643step1Labels permutation14 hz
    mixedMoment B raw19643step2 raw19643step2Labels = mixedMoment B raw19643step3 raw19643step3Labels := by
      have ha : raw19643step3 = (fun i j => raw19643step2 (permutation7 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19643step3 raw19643step2; decide +kernel
      have hl : raw19643step3Labels = raw19643step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19643step2 raw19643step2Labels permutation7 permutation3
    mixedMoment B raw19643step3 raw19643step3Labels = mixedMoment B raw19643step4 raw19643step4Labels := by
      have ha : raw19643step4 = -raw19643step3 := by apply Matrix.ext; change ∀ i j, raw19643step4 i j = -(raw19643step3 i j); unfold raw19643step4 raw19643step3; decide +kernel
      have hl : raw19643step4Labels = raw19643step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1450 node1450Labels := by rfl

def raw19644 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19644Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19644step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19644step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19644step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19644step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19644step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![4, -3, -1]]
def raw19644step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19644 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19644 raw19644Labels = mixedMoment B node587 node587Labels := by
  calc
    mixedMoment B raw19644 raw19644Labels = mixedMoment B raw19644step0 raw19644step0Labels := by
      have hz : ∀ j, raw19644 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19644step0 = (fun i j => raw19644 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19644step0 raw19644; decide +kernel
      have hl : raw19644step0Labels = raw19644Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19644 raw19644Labels permutation434 hz
    mixedMoment B raw19644step0 raw19644step0Labels = mixedMoment B raw19644step1 raw19644step1Labels := by
      have hz : ∀ j, raw19644step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19644step1 = (fun i j => raw19644step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19644step1 raw19644step0; decide +kernel
      have hl : raw19644step1Labels = raw19644step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19644step0 raw19644step0Labels permutation80 hz
    mixedMoment B raw19644step1 raw19644step1Labels = mixedMoment B raw19644step2 raw19644step2Labels := by
      have ha : raw19644step2 = (fun i j => raw19644step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19644step2 raw19644step1; decide +kernel
      have hl : raw19644step2Labels = raw19644step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19644step1 raw19644step1Labels permutation10 permutation3
    _ = mixedMoment B node587 node587Labels := by rfl

def raw19645 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19645Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19645step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19645step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19645step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![4, -3, -1]]
def raw19645step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19645 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19645 raw19645Labels = mixedMoment B node1118 node1118Labels := by
  calc
    mixedMoment B raw19645 raw19645Labels = mixedMoment B raw19645step0 raw19645step0Labels := by
      have hz : ∀ j, raw19645 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19645step0 = (fun i j => raw19645 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19645step0 raw19645; decide +kernel
      have hl : raw19645step0Labels = raw19645Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19645 raw19645Labels permutation434 hz
    mixedMoment B raw19645step0 raw19645step0Labels = mixedMoment B raw19645step1 raw19645step1Labels := by
      have ha : raw19645step1 = (fun i j => raw19645step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19645step1 raw19645step0; decide +kernel
      have hl : raw19645step1Labels = raw19645step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19645step0 raw19645step0Labels permutation40 permutation3
    _ = mixedMoment B node1118 node1118Labels := by rfl

def raw19646 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19646Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19646step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19646step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19646step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![4, -3, -1]]
def raw19646step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19646 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19646 raw19646Labels = mixedMoment B node1118 node1118Labels := by
  calc
    mixedMoment B raw19646 raw19646Labels = mixedMoment B raw19646step0 raw19646step0Labels := by
      have hz : ∀ j, raw19646 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19646step0 = (fun i j => raw19646 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19646step0 raw19646; decide +kernel
      have hl : raw19646step0Labels = raw19646Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19646 raw19646Labels permutation346 hz
    mixedMoment B raw19646step0 raw19646step0Labels = mixedMoment B raw19646step1 raw19646step1Labels := by
      have ha : raw19646step1 = (fun i j => raw19646step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19646step1 raw19646step0; decide +kernel
      have hl : raw19646step1Labels = raw19646step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19646step0 raw19646step0Labels permutation40 permutation3
    _ = mixedMoment B node1118 node1118Labels := by rfl

def raw19647 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![4, -1, -3]]
def raw19647Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19647step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![4, -1, -3]]
def raw19647step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19647step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 0, 1], ![4, -1, -3]]
def raw19647step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19647step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![4, -3, -1]]
def raw19647step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19647 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19647 raw19647Labels = mixedMoment B node1173 node1173Labels := by
  calc
    mixedMoment B raw19647 raw19647Labels = mixedMoment B raw19647step0 raw19647step0Labels := by
      have hz : ∀ j, raw19647 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19647step0 = (fun i j => raw19647 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19647step0 raw19647; decide +kernel
      have hl : raw19647step0Labels = raw19647Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19647 raw19647Labels permutation434 hz
    mixedMoment B raw19647step0 raw19647step0Labels = mixedMoment B raw19647step1 raw19647step1Labels := by
      have hz : ∀ j, raw19647step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19647step1 = (fun i j => raw19647step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19647step1 raw19647step0; decide +kernel
      have hl : raw19647step1Labels = raw19647step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19647step0 raw19647step0Labels permutation80 hz
    mixedMoment B raw19647step1 raw19647step1Labels = mixedMoment B raw19647step2 raw19647step2Labels := by
      have ha : raw19647step2 = (fun i j => raw19647step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19647step2 raw19647step1; decide +kernel
      have hl : raw19647step2Labels = raw19647step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19647step1 raw19647step1Labels permutation10 permutation3
    _ = mixedMoment B node1173 node1173Labels := by rfl

def raw19648 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw19648Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19648step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw19648step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19648step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw19648step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19648step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw19648step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19648 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19648 raw19648Labels = mixedMoment B node1271 node1271Labels := by
  calc
    mixedMoment B raw19648 raw19648Labels = mixedMoment B raw19648step0 raw19648step0Labels := by
      have hz : ∀ j, raw19648 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19648step0 = (fun i j => raw19648 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19648step0 raw19648; decide +kernel
      have hl : raw19648step0Labels = raw19648Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19648 raw19648Labels permutation434 hz
    mixedMoment B raw19648step0 raw19648step0Labels = mixedMoment B raw19648step1 raw19648step1Labels := by
      have hz : ∀ j, raw19648step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19648step1 = (fun i j => raw19648step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19648step1 raw19648step0; decide +kernel
      have hl : raw19648step1Labels = raw19648step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19648step0 raw19648step0Labels permutation80 hz
    mixedMoment B raw19648step1 raw19648step1Labels = mixedMoment B raw19648step2 raw19648step2Labels := by
      have ha : raw19648step2 = (fun i j => raw19648step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19648step2 raw19648step1; decide +kernel
      have hl : raw19648step2Labels = raw19648step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19648step1 raw19648step1Labels permutation10 permutation3
    _ = mixedMoment B node1271 node1271Labels := by rfl

def raw19649 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19649Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19649step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19649step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19649step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19649step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19649step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![4, -3, -1]]
def raw19649step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19649 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19649 raw19649Labels = mixedMoment B node587 node587Labels := by
  calc
    mixedMoment B raw19649 raw19649Labels = mixedMoment B raw19649step0 raw19649step0Labels := by
      have hz : ∀ j, raw19649 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19649step0 = (fun i j => raw19649 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19649step0 raw19649; decide +kernel
      have hl : raw19649step0Labels = raw19649Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19649 raw19649Labels permutation434 hz
    mixedMoment B raw19649step0 raw19649step0Labels = mixedMoment B raw19649step1 raw19649step1Labels := by
      have hz : ∀ j, raw19649step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19649step1 = (fun i j => raw19649step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19649step1 raw19649step0; decide +kernel
      have hl : raw19649step1Labels = raw19649step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19649step0 raw19649step0Labels permutation56 hz
    mixedMoment B raw19649step1 raw19649step1Labels = mixedMoment B raw19649step2 raw19649step2Labels := by
      have ha : raw19649step2 = (fun i j => raw19649step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19649step2 raw19649step1; decide +kernel
      have hl : raw19649step2Labels = raw19649step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19649step1 raw19649step1Labels permutation10 permutation3
    _ = mixedMoment B node587 node587Labels := by rfl

def raw19650 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19650Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19650step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19650step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19650step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![4, -3, -1]]
def raw19650step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19650 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19650 raw19650Labels = mixedMoment B node1118 node1118Labels := by
  calc
    mixedMoment B raw19650 raw19650Labels = mixedMoment B raw19650step0 raw19650step0Labels := by
      have hz : ∀ j, raw19650 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19650step0 = (fun i j => raw19650 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19650step0 raw19650; decide +kernel
      have hl : raw19650step0Labels = raw19650Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19650 raw19650Labels permutation434 hz
    mixedMoment B raw19650step0 raw19650step0Labels = mixedMoment B raw19650step1 raw19650step1Labels := by
      have ha : raw19650step1 = (fun i j => raw19650step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19650step1 raw19650step0; decide +kernel
      have hl : raw19650step1Labels = raw19650step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19650step0 raw19650step0Labels permutation34 permutation3
    _ = mixedMoment B node1118 node1118Labels := by rfl

def raw19651 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19651Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19651step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19651step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19651step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![4, -3, -1]]
def raw19651step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19651 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19651 raw19651Labels = mixedMoment B node1118 node1118Labels := by
  calc
    mixedMoment B raw19651 raw19651Labels = mixedMoment B raw19651step0 raw19651step0Labels := by
      have hz : ∀ j, raw19651 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw19651step0 = (fun i j => raw19651 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw19651step0 raw19651; decide +kernel
      have hl : raw19651step0Labels = raw19651Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19651 raw19651Labels permutation265 hz
    mixedMoment B raw19651step0 raw19651step0Labels = mixedMoment B raw19651step1 raw19651step1Labels := by
      have ha : raw19651step1 = (fun i j => raw19651step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19651step1 raw19651step0; decide +kernel
      have hl : raw19651step1Labels = raw19651step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19651step0 raw19651step0Labels permutation40 permutation3
    _ = mixedMoment B node1118 node1118Labels := by rfl

def raw19652 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![4, -1, -3]]
def raw19652Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19652step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![4, -1, -3]]
def raw19652step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19652step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 0, 1], ![4, -1, -3]]
def raw19652step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19652step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![4, -3, -1]]
def raw19652step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19652 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19652 raw19652Labels = mixedMoment B node1173 node1173Labels := by
  calc
    mixedMoment B raw19652 raw19652Labels = mixedMoment B raw19652step0 raw19652step0Labels := by
      have hz : ∀ j, raw19652 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19652step0 = (fun i j => raw19652 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19652step0 raw19652; decide +kernel
      have hl : raw19652step0Labels = raw19652Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19652 raw19652Labels permutation434 hz
    mixedMoment B raw19652step0 raw19652step0Labels = mixedMoment B raw19652step1 raw19652step1Labels := by
      have hz : ∀ j, raw19652step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19652step1 = (fun i j => raw19652step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19652step1 raw19652step0; decide +kernel
      have hl : raw19652step1Labels = raw19652step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19652step0 raw19652step0Labels permutation56 hz
    mixedMoment B raw19652step1 raw19652step1Labels = mixedMoment B raw19652step2 raw19652step2Labels := by
      have ha : raw19652step2 = (fun i j => raw19652step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19652step2 raw19652step1; decide +kernel
      have hl : raw19652step2Labels = raw19652step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19652step1 raw19652step1Labels permutation10 permutation3
    _ = mixedMoment B node1173 node1173Labels := by rfl

def raw19653 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw19653Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19653step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw19653step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19653step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw19653step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19653step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw19653step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19653 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19653 raw19653Labels = mixedMoment B node1271 node1271Labels := by
  calc
    mixedMoment B raw19653 raw19653Labels = mixedMoment B raw19653step0 raw19653step0Labels := by
      have hz : ∀ j, raw19653 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19653step0 = (fun i j => raw19653 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19653step0 raw19653; decide +kernel
      have hl : raw19653step0Labels = raw19653Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19653 raw19653Labels permutation434 hz
    mixedMoment B raw19653step0 raw19653step0Labels = mixedMoment B raw19653step1 raw19653step1Labels := by
      have hz : ∀ j, raw19653step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19653step1 = (fun i j => raw19653step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19653step1 raw19653step0; decide +kernel
      have hl : raw19653step1Labels = raw19653step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19653step0 raw19653step0Labels permutation56 hz
    mixedMoment B raw19653step1 raw19653step1Labels = mixedMoment B raw19653step2 raw19653step2Labels := by
      have ha : raw19653step2 = (fun i j => raw19653step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19653step2 raw19653step1; decide +kernel
      have hl : raw19653step2Labels = raw19653step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19653step1 raw19653step1Labels permutation10 permutation3
    _ = mixedMoment B node1271 node1271Labels := by rfl

def raw19654 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19654Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19654step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19654step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19654step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19654step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19654step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![4, -3, -1]]
def raw19654step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19654 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19654 raw19654Labels = mixedMoment B node587 node587Labels := by
  calc
    mixedMoment B raw19654 raw19654Labels = mixedMoment B raw19654step0 raw19654step0Labels := by
      have hz : ∀ j, raw19654 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19654step0 = (fun i j => raw19654 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19654step0 raw19654; decide +kernel
      have hl : raw19654step0Labels = raw19654Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19654 raw19654Labels permutation346 hz
    mixedMoment B raw19654step0 raw19654step0Labels = mixedMoment B raw19654step1 raw19654step1Labels := by
      have hz : ∀ j, raw19654step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19654step1 = (fun i j => raw19654step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19654step1 raw19654step0; decide +kernel
      have hl : raw19654step1Labels = raw19654step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19654step0 raw19654step0Labels permutation56 hz
    mixedMoment B raw19654step1 raw19654step1Labels = mixedMoment B raw19654step2 raw19654step2Labels := by
      have ha : raw19654step2 = (fun i j => raw19654step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19654step2 raw19654step1; decide +kernel
      have hl : raw19654step2Labels = raw19654step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19654step1 raw19654step1Labels permutation10 permutation3
    _ = mixedMoment B node587 node587Labels := by rfl

def raw19655 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19655Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19655step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19655step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19655step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![4, -3, -1]]
def raw19655step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19655 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19655 raw19655Labels = mixedMoment B node1118 node1118Labels := by
  calc
    mixedMoment B raw19655 raw19655Labels = mixedMoment B raw19655step0 raw19655step0Labels := by
      have hz : ∀ j, raw19655 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19655step0 = (fun i j => raw19655 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19655step0 raw19655; decide +kernel
      have hl : raw19655step0Labels = raw19655Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19655 raw19655Labels permutation346 hz
    mixedMoment B raw19655step0 raw19655step0Labels = mixedMoment B raw19655step1 raw19655step1Labels := by
      have ha : raw19655step1 = (fun i j => raw19655step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19655step1 raw19655step0; decide +kernel
      have hl : raw19655step1Labels = raw19655step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19655step0 raw19655step0Labels permutation34 permutation3
    _ = mixedMoment B node1118 node1118Labels := by rfl

def raw19656 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19656Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19656step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19656step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19656step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![4, -3, -1]]
def raw19656step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19656 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19656 raw19656Labels = mixedMoment B node1118 node1118Labels := by
  calc
    mixedMoment B raw19656 raw19656Labels = mixedMoment B raw19656step0 raw19656step0Labels := by
      have hz : ∀ j, raw19656 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw19656step0 = (fun i j => raw19656 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw19656step0 raw19656; decide +kernel
      have hl : raw19656step0Labels = raw19656Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19656 raw19656Labels permutation265 hz
    mixedMoment B raw19656step0 raw19656step0Labels = mixedMoment B raw19656step1 raw19656step1Labels := by
      have ha : raw19656step1 = (fun i j => raw19656step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19656step1 raw19656step0; decide +kernel
      have hl : raw19656step1Labels = raw19656step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19656step0 raw19656step0Labels permutation34 permutation3
    _ = mixedMoment B node1118 node1118Labels := by rfl

def raw19657 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![4, -1, -3]]
def raw19657Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19657step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![4, -1, -3]]
def raw19657step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19657step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 0, 1], ![4, -1, -3]]
def raw19657step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19657step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![4, -3, -1]]
def raw19657step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19657 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19657 raw19657Labels = mixedMoment B node1173 node1173Labels := by
  calc
    mixedMoment B raw19657 raw19657Labels = mixedMoment B raw19657step0 raw19657step0Labels := by
      have hz : ∀ j, raw19657 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19657step0 = (fun i j => raw19657 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19657step0 raw19657; decide +kernel
      have hl : raw19657step0Labels = raw19657Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19657 raw19657Labels permutation346 hz
    mixedMoment B raw19657step0 raw19657step0Labels = mixedMoment B raw19657step1 raw19657step1Labels := by
      have hz : ∀ j, raw19657step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19657step1 = (fun i j => raw19657step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19657step1 raw19657step0; decide +kernel
      have hl : raw19657step1Labels = raw19657step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19657step0 raw19657step0Labels permutation56 hz
    mixedMoment B raw19657step1 raw19657step1Labels = mixedMoment B raw19657step2 raw19657step2Labels := by
      have ha : raw19657step2 = (fun i j => raw19657step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19657step2 raw19657step1; decide +kernel
      have hl : raw19657step2Labels = raw19657step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19657step1 raw19657step1Labels permutation10 permutation3
    _ = mixedMoment B node1173 node1173Labels := by rfl

def raw19658 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw19658Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19658step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw19658step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19658step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw19658step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19658step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw19658step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19658 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19658 raw19658Labels = mixedMoment B node1271 node1271Labels := by
  calc
    mixedMoment B raw19658 raw19658Labels = mixedMoment B raw19658step0 raw19658step0Labels := by
      have hz : ∀ j, raw19658 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19658step0 = (fun i j => raw19658 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19658step0 raw19658; decide +kernel
      have hl : raw19658step0Labels = raw19658Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19658 raw19658Labels permutation346 hz
    mixedMoment B raw19658step0 raw19658step0Labels = mixedMoment B raw19658step1 raw19658step1Labels := by
      have hz : ∀ j, raw19658step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19658step1 = (fun i j => raw19658step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19658step1 raw19658step0; decide +kernel
      have hl : raw19658step1Labels = raw19658step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19658step0 raw19658step0Labels permutation56 hz
    mixedMoment B raw19658step1 raw19658step1Labels = mixedMoment B raw19658step2 raw19658step2Labels := by
      have ha : raw19658step2 = (fun i j => raw19658step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19658step2 raw19658step1; decide +kernel
      have hl : raw19658step2Labels = raw19658step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19658step1 raw19658step1Labels permutation10 permutation3
    _ = mixedMoment B node1271 node1271Labels := by rfl

def raw19659 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![4, -1, -3]]
def raw19659Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19659step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![4, -1, -3]]
def raw19659step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19659step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -2, 1], ![4, -1, -3]]
def raw19659step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19659step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -2, 1], ![4, -1, -3]]
def raw19659step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19659step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 1, -2], ![4, -3, -1]]
def raw19659step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19659 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19659 raw19659Labels = mixedMoment B node617 node617Labels := by
  calc
    mixedMoment B raw19659 raw19659Labels = mixedMoment B raw19659step0 raw19659step0Labels := by
      have hz : ∀ j, raw19659 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19659step0 = (fun i j => raw19659 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19659step0 raw19659; decide +kernel
      have hl : raw19659step0Labels = raw19659Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19659 raw19659Labels permutation434 hz
    mixedMoment B raw19659step0 raw19659step0Labels = mixedMoment B raw19659step1 raw19659step1Labels := by
      have hz : ∀ j, raw19659step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19659step1 = (fun i j => raw19659step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19659step1 raw19659step0; decide +kernel
      have hl : raw19659step1Labels = raw19659step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19659step0 raw19659step0Labels permutation80 hz
    mixedMoment B raw19659step1 raw19659step1Labels = mixedMoment B raw19659step2 raw19659step2Labels := by
      have hz : ∀ j, raw19659step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19659step2 = (fun i j => raw19659step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19659step2 raw19659step1; decide +kernel
      have hl : raw19659step2Labels = raw19659step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19659step1 raw19659step1Labels permutation14 hz
    mixedMoment B raw19659step2 raw19659step2Labels = mixedMoment B raw19659step3 raw19659step3Labels := by
      have ha : raw19659step3 = (fun i j => raw19659step2 (permutation2 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19659step3 raw19659step2; decide +kernel
      have hl : raw19659step3Labels = raw19659step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19659step2 raw19659step2Labels permutation2 permutation3
    _ = mixedMoment B node617 node617Labels := by rfl

def raw19660 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![4, -1, -3]]
def raw19660Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19660step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![4, -1, -3]]
def raw19660step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19660step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -2, 1], ![4, -1, -3]]
def raw19660step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19660step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 1, -2], ![4, -3, -1]]
def raw19660step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19660 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19660 raw19660Labels = mixedMoment B node1142 node1142Labels := by
  calc
    mixedMoment B raw19660 raw19660Labels = mixedMoment B raw19660step0 raw19660step0Labels := by
      have hz : ∀ j, raw19660 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19660step0 = (fun i j => raw19660 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19660step0 raw19660; decide +kernel
      have hl : raw19660step0Labels = raw19660Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19660 raw19660Labels permutation434 hz
    mixedMoment B raw19660step0 raw19660step0Labels = mixedMoment B raw19660step1 raw19660step1Labels := by
      have hz : ∀ j, raw19660step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19660step1 = (fun i j => raw19660step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19660step1 raw19660step0; decide +kernel
      have hl : raw19660step1Labels = raw19660step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19660step0 raw19660step0Labels permutation80 hz
    mixedMoment B raw19660step1 raw19660step1Labels = mixedMoment B raw19660step2 raw19660step2Labels := by
      have ha : raw19660step2 = (fun i j => raw19660step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19660step2 raw19660step1; decide +kernel
      have hl : raw19660step2Labels = raw19660step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19660step1 raw19660step1Labels permutation8 permutation3
    _ = mixedMoment B node1142 node1142Labels := by rfl

def raw19661 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![4, -1, -3]]
def raw19661Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19661step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![4, -1, -3]]
def raw19661step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19661step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -2, 1], ![4, -1, -3]]
def raw19661step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19661step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 1, -2], ![4, -3, -1]]
def raw19661step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19661 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19661 raw19661Labels = mixedMoment B node1142 node1142Labels := by
  calc
    mixedMoment B raw19661 raw19661Labels = mixedMoment B raw19661step0 raw19661step0Labels := by
      have hz : ∀ j, raw19661 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19661step0 = (fun i j => raw19661 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19661step0 raw19661; decide +kernel
      have hl : raw19661step0Labels = raw19661Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19661 raw19661Labels permutation434 hz
    mixedMoment B raw19661step0 raw19661step0Labels = mixedMoment B raw19661step1 raw19661step1Labels := by
      have hz : ∀ j, raw19661step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19661step1 = (fun i j => raw19661step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19661step1 raw19661step0; decide +kernel
      have hl : raw19661step1Labels = raw19661step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19661step0 raw19661step0Labels permutation56 hz
    mixedMoment B raw19661step1 raw19661step1Labels = mixedMoment B raw19661step2 raw19661step2Labels := by
      have ha : raw19661step2 = (fun i j => raw19661step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19661step2 raw19661step1; decide +kernel
      have hl : raw19661step2Labels = raw19661step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19661step1 raw19661step1Labels permutation8 permutation3
    _ = mixedMoment B node1142 node1142Labels := by rfl

def raw19662 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![4, -1, -3]]
def raw19662Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19662step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![4, -1, -3]]
def raw19662step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19662step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -2, 1], ![4, -1, -3]]
def raw19662step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19662step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 1, -2], ![4, -3, -1]]
def raw19662step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19662 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19662 raw19662Labels = mixedMoment B node1142 node1142Labels := by
  calc
    mixedMoment B raw19662 raw19662Labels = mixedMoment B raw19662step0 raw19662step0Labels := by
      have hz : ∀ j, raw19662 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19662step0 = (fun i j => raw19662 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19662step0 raw19662; decide +kernel
      have hl : raw19662step0Labels = raw19662Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19662 raw19662Labels permutation346 hz
    mixedMoment B raw19662step0 raw19662step0Labels = mixedMoment B raw19662step1 raw19662step1Labels := by
      have hz : ∀ j, raw19662step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19662step1 = (fun i j => raw19662step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19662step1 raw19662step0; decide +kernel
      have hl : raw19662step1Labels = raw19662step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19662step0 raw19662step0Labels permutation56 hz
    mixedMoment B raw19662step1 raw19662step1Labels = mixedMoment B raw19662step2 raw19662step2Labels := by
      have ha : raw19662step2 = (fun i j => raw19662step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19662step2 raw19662step1; decide +kernel
      have hl : raw19662step2Labels = raw19662step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19662step1 raw19662step1Labels permutation8 permutation3
    _ = mixedMoment B node1142 node1142Labels := by rfl

def raw19663 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![5, -2, -3]]
def raw19663Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19663step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![5, -2, -3]]
def raw19663step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19663step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, -1, 1], ![5, -2, -3]]
def raw19663step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19663step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![5, -2, -3]]
def raw19663step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19663step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![5, -3, -2]]
def raw19663step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19663 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19663 raw19663Labels = mixedMoment B node591 node591Labels := by
  calc
    mixedMoment B raw19663 raw19663Labels = mixedMoment B raw19663step0 raw19663step0Labels := by
      have hz : ∀ j, raw19663 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19663step0 = (fun i j => raw19663 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19663step0 raw19663; decide +kernel
      have hl : raw19663step0Labels = raw19663Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19663 raw19663Labels permutation434 hz
    mixedMoment B raw19663step0 raw19663step0Labels = mixedMoment B raw19663step1 raw19663step1Labels := by
      have hz : ∀ j, raw19663step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19663step1 = (fun i j => raw19663step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19663step1 raw19663step0; decide +kernel
      have hl : raw19663step1Labels = raw19663step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19663step0 raw19663step0Labels permutation80 hz
    mixedMoment B raw19663step1 raw19663step1Labels = mixedMoment B raw19663step2 raw19663step2Labels := by
      have hz : ∀ j, raw19663step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19663step2 = (fun i j => raw19663step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19663step2 raw19663step1; decide +kernel
      have hl : raw19663step2Labels = raw19663step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19663step1 raw19663step1Labels permutation14 hz
    mixedMoment B raw19663step2 raw19663step2Labels = mixedMoment B raw19663step3 raw19663step3Labels := by
      have ha : raw19663step3 = (fun i j => raw19663step2 (permutation2 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19663step3 raw19663step2; decide +kernel
      have hl : raw19663step3Labels = raw19663step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19663step2 raw19663step2Labels permutation2 permutation3
    _ = mixedMoment B node591 node591Labels := by rfl

def raw19664 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![5, -2, -3]]
def raw19664Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19664step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![5, -2, -3]]
def raw19664step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19664step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![5, -2, -3]]
def raw19664step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19664step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![5, -3, -2], ![0, 1, -1], ![-1, 0, 1], ![-4, 2, 2]]
def raw19664step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19664step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, 0, -1], ![4, -2, -2]]
def raw19664step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19664 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19664 raw19664Labels = mixedMoment B node633 node633Labels := by
  calc
    mixedMoment B raw19664 raw19664Labels = mixedMoment B raw19664step0 raw19664step0Labels := by
      have hz : ∀ j, raw19664 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19664step0 = (fun i j => raw19664 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19664step0 raw19664; decide +kernel
      have hl : raw19664step0Labels = raw19664Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19664 raw19664Labels permutation434 hz
    mixedMoment B raw19664step0 raw19664step0Labels = mixedMoment B raw19664step1 raw19664step1Labels := by
      have hz : ∀ j, raw19664step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19664step1 = (fun i j => raw19664step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19664step1 raw19664step0; decide +kernel
      have hl : raw19664step1Labels = raw19664step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19664step0 raw19664step0Labels permutation80 hz
    mixedMoment B raw19664step1 raw19664step1Labels = mixedMoment B raw19664step2 raw19664step2Labels := by
      have ha : raw19664step2 = (fun i j => raw19664step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19664step2 raw19664step1; decide +kernel
      have hl : raw19664step2Labels = raw19664step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19664step1 raw19664step1Labels permutation31 permutation3
    mixedMoment B raw19664step2 raw19664step2Labels = mixedMoment B raw19664step3 raw19664step3Labels := by
      have ha : raw19664step3 = -raw19664step2 := by apply Matrix.ext; change ∀ i j, raw19664step3 i j = -(raw19664step2 i j); unfold raw19664step3 raw19664step2; decide +kernel
      have hl : raw19664step3Labels = raw19664step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node633 node633Labels := by rfl

def raw19665 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![5, -2, -3]]
def raw19665Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19665step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![5, -2, -3]]
def raw19665step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19665step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![5, -2, -3]]
def raw19665step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19665step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![5, -3, -2], ![0, 1, -1], ![-1, 0, 1], ![-4, 2, 2]]
def raw19665step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19665step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, 0, -1], ![4, -2, -2]]
def raw19665step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19665 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19665 raw19665Labels = mixedMoment B node633 node633Labels := by
  calc
    mixedMoment B raw19665 raw19665Labels = mixedMoment B raw19665step0 raw19665step0Labels := by
      have hz : ∀ j, raw19665 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19665step0 = (fun i j => raw19665 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19665step0 raw19665; decide +kernel
      have hl : raw19665step0Labels = raw19665Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19665 raw19665Labels permutation434 hz
    mixedMoment B raw19665step0 raw19665step0Labels = mixedMoment B raw19665step1 raw19665step1Labels := by
      have hz : ∀ j, raw19665step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19665step1 = (fun i j => raw19665step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19665step1 raw19665step0; decide +kernel
      have hl : raw19665step1Labels = raw19665step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19665step0 raw19665step0Labels permutation56 hz
    mixedMoment B raw19665step1 raw19665step1Labels = mixedMoment B raw19665step2 raw19665step2Labels := by
      have ha : raw19665step2 = (fun i j => raw19665step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19665step2 raw19665step1; decide +kernel
      have hl : raw19665step2Labels = raw19665step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19665step1 raw19665step1Labels permutation31 permutation3
    mixedMoment B raw19665step2 raw19665step2Labels = mixedMoment B raw19665step3 raw19665step3Labels := by
      have ha : raw19665step3 = -raw19665step2 := by apply Matrix.ext; change ∀ i j, raw19665step3 i j = -(raw19665step2 i j); unfold raw19665step3 raw19665step2; decide +kernel
      have hl : raw19665step3Labels = raw19665step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node633 node633Labels := by rfl

def raw19666 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![5, -2, -3]]
def raw19666Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19666step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![5, -2, -3]]
def raw19666step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19666step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![5, -2, -3]]
def raw19666step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19666step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![5, -3, -2], ![0, 1, -1], ![-1, 0, 1], ![-4, 2, 2]]
def raw19666step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19666step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, 0, -1], ![4, -2, -2]]
def raw19666step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19666 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19666 raw19666Labels = mixedMoment B node633 node633Labels := by
  calc
    mixedMoment B raw19666 raw19666Labels = mixedMoment B raw19666step0 raw19666step0Labels := by
      have hz : ∀ j, raw19666 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19666step0 = (fun i j => raw19666 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19666step0 raw19666; decide +kernel
      have hl : raw19666step0Labels = raw19666Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19666 raw19666Labels permutation346 hz
    mixedMoment B raw19666step0 raw19666step0Labels = mixedMoment B raw19666step1 raw19666step1Labels := by
      have hz : ∀ j, raw19666step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19666step1 = (fun i j => raw19666step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19666step1 raw19666step0; decide +kernel
      have hl : raw19666step1Labels = raw19666step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19666step0 raw19666step0Labels permutation56 hz
    mixedMoment B raw19666step1 raw19666step1Labels = mixedMoment B raw19666step2 raw19666step2Labels := by
      have ha : raw19666step2 = (fun i j => raw19666step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19666step2 raw19666step1; decide +kernel
      have hl : raw19666step2Labels = raw19666step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19666step1 raw19666step1Labels permutation31 permutation3
    mixedMoment B raw19666step2 raw19666step2Labels = mixedMoment B raw19666step3 raw19666step3Labels := by
      have ha : raw19666step3 = -raw19666step2 := by apply Matrix.ext; change ∀ i j, raw19666step3 i j = -(raw19666step2 i j); unfold raw19666step3 raw19666step2; decide +kernel
      have hl : raw19666step3Labels = raw19666step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node633 node633Labels := by rfl

def raw19667 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![5, -2, -3]]
def raw19667Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19667step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![5, -2, -3]]
def raw19667step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19667step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 0, 1], ![5, -2, -3]]
def raw19667step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19667step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![5, -2, -3]]
def raw19667step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19667step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![5, -3, -2], ![-1, 1, 0], ![-4, 2, 2]]
def raw19667step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19667step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![4, -2, -2]]
def raw19667step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19667 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19667 raw19667Labels = mixedMoment B node650 node650Labels := by
  calc
    mixedMoment B raw19667 raw19667Labels = mixedMoment B raw19667step0 raw19667step0Labels := by
      have hz : ∀ j, raw19667 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19667step0 = (fun i j => raw19667 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19667step0 raw19667; decide +kernel
      have hl : raw19667step0Labels = raw19667Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19667 raw19667Labels permutation434 hz
    mixedMoment B raw19667step0 raw19667step0Labels = mixedMoment B raw19667step1 raw19667step1Labels := by
      have hz : ∀ j, raw19667step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19667step1 = (fun i j => raw19667step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19667step1 raw19667step0; decide +kernel
      have hl : raw19667step1Labels = raw19667step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19667step0 raw19667step0Labels permutation80 hz
    mixedMoment B raw19667step1 raw19667step1Labels = mixedMoment B raw19667step2 raw19667step2Labels := by
      have hz : ∀ j, raw19667step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19667step2 = (fun i j => raw19667step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19667step2 raw19667step1; decide +kernel
      have hl : raw19667step2Labels = raw19667step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19667step1 raw19667step1Labels permutation14 hz
    mixedMoment B raw19667step2 raw19667step2Labels = mixedMoment B raw19667step3 raw19667step3Labels := by
      have ha : raw19667step3 = (fun i j => raw19667step2 (permutation7 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19667step3 raw19667step2; decide +kernel
      have hl : raw19667step3Labels = raw19667step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19667step2 raw19667step2Labels permutation7 permutation3
    mixedMoment B raw19667step3 raw19667step3Labels = mixedMoment B raw19667step4 raw19667step4Labels := by
      have ha : raw19667step4 = -raw19667step3 := by apply Matrix.ext; change ∀ i j, raw19667step4 i j = -(raw19667step3 i j); unfold raw19667step4 raw19667step3; decide +kernel
      have hl : raw19667step4Labels = raw19667step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node650 node650Labels := by rfl

def raw19668 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19668Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19668step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19668step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19668step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19668step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19668step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![-1, 1, 0], ![-1, 0, 1], ![-1, -3, 4]]
def raw19668step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19668step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![1, -1, 0], ![1, 0, -1], ![1, 3, -4]]
def raw19668step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19668step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![1, -1, 0], ![1, 0, -1], ![1, 3, -4]]
def raw19668step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19668 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19668 raw19668Labels = mixedMoment B node1532 node1532Labels := by
  calc
    mixedMoment B raw19668 raw19668Labels = mixedMoment B raw19668step0 raw19668step0Labels := by
      have hz : ∀ j, raw19668 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19668step0 = (fun i j => raw19668 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19668step0 raw19668; decide +kernel
      have hl : raw19668step0Labels = raw19668Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19668 raw19668Labels permutation434 hz
    mixedMoment B raw19668step0 raw19668step0Labels = mixedMoment B raw19668step1 raw19668step1Labels := by
      have hz : ∀ j, raw19668step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19668step1 = (fun i j => raw19668step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19668step1 raw19668step0; decide +kernel
      have hl : raw19668step1Labels = raw19668step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19668step0 raw19668step0Labels permutation80 hz
    mixedMoment B raw19668step1 raw19668step1Labels = mixedMoment B raw19668step2 raw19668step2Labels := by
      have ha : raw19668step2 = (fun i j => raw19668step1 (permutation10 i) (permutation5 j)) := by apply Matrix.ext; unfold raw19668step2 raw19668step1; decide +kernel
      have hl : raw19668step2Labels = raw19668step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19668step1 raw19668step1Labels permutation10 permutation5
    mixedMoment B raw19668step2 raw19668step2Labels = mixedMoment B raw19668step3 raw19668step3Labels := by
      have ha : raw19668step3 = -raw19668step2 := by apply Matrix.ext; change ∀ i j, raw19668step3 i j = -(raw19668step2 i j); unfold raw19668step3 raw19668step2; decide +kernel
      have hl : raw19668step3Labels = raw19668step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19668step3 raw19668step3Labels = mixedMoment B raw19668step4 raw19668step4Labels := by
      have ha : raw19668step4 = raw19668step3 := by apply Matrix.ext; unfold raw19668step4 raw19668step3; decide +kernel
      have hl : raw19668step3Labels = labelEmbedding1 ∘ raw19668step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19668step3 raw19668step3Labels raw19668step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1532 node1532Labels := by rfl

def raw19669 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19669Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19669step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19669step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19669step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw19669step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19669step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw19669step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19669 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19669 raw19669Labels = mixedMoment B node1672 node1672Labels := by
  calc
    mixedMoment B raw19669 raw19669Labels = mixedMoment B raw19669step0 raw19669step0Labels := by
      have hz : ∀ j, raw19669 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19669step0 = (fun i j => raw19669 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19669step0 raw19669; decide +kernel
      have hl : raw19669step0Labels = raw19669Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19669 raw19669Labels permutation434 hz
    mixedMoment B raw19669step0 raw19669step0Labels = mixedMoment B raw19669step1 raw19669step1Labels := by
      have ha : raw19669step1 = (fun i j => raw19669step0 (permutation137 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19669step1 raw19669step0; decide +kernel
      have hl : raw19669step1Labels = raw19669step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19669step0 raw19669step0Labels permutation137 permutation7
    mixedMoment B raw19669step1 raw19669step1Labels = mixedMoment B raw19669step2 raw19669step2Labels := by
      have ha : raw19669step2 = raw19669step1 := by apply Matrix.ext; unfold raw19669step2 raw19669step1; decide +kernel
      have hl : raw19669step1Labels = labelEmbedding1 ∘ raw19669step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19669step1 raw19669step1Labels raw19669step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1672 node1672Labels := by rfl

def raw19670 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19670Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19670step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19670step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19670step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw19670step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19670step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw19670step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19670 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19670 raw19670Labels = mixedMoment B node1672 node1672Labels := by
  calc
    mixedMoment B raw19670 raw19670Labels = mixedMoment B raw19670step0 raw19670step0Labels := by
      have hz : ∀ j, raw19670 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19670step0 = (fun i j => raw19670 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19670step0 raw19670; decide +kernel
      have hl : raw19670step0Labels = raw19670Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19670 raw19670Labels permutation346 hz
    mixedMoment B raw19670step0 raw19670step0Labels = mixedMoment B raw19670step1 raw19670step1Labels := by
      have ha : raw19670step1 = (fun i j => raw19670step0 (permutation137 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19670step1 raw19670step0; decide +kernel
      have hl : raw19670step1Labels = raw19670step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19670step0 raw19670step0Labels permutation137 permutation7
    mixedMoment B raw19670step1 raw19670step1Labels = mixedMoment B raw19670step2 raw19670step2Labels := by
      have ha : raw19670step2 = raw19670step1 := by apply Matrix.ext; unfold raw19670step2 raw19670step1; decide +kernel
      have hl : raw19670step1Labels = labelEmbedding1 ∘ raw19670step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19670step1 raw19670step1Labels raw19670step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1672 node1672Labels := by rfl

def raw19671 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![4, -1, -3]]
def raw19671Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19671step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![4, -1, -3]]
def raw19671step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19671step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 0, 1], ![4, -1, -3]]
def raw19671step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19671step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 0, -1], ![2, 2, -4]]
def raw19671step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19671step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 0, -1], ![2, 2, -4]]
def raw19671step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19671 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19671 raw19671Labels = mixedMoment B node1692 node1692Labels := by
  calc
    mixedMoment B raw19671 raw19671Labels = mixedMoment B raw19671step0 raw19671step0Labels := by
      have hz : ∀ j, raw19671 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19671step0 = (fun i j => raw19671 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19671step0 raw19671; decide +kernel
      have hl : raw19671step0Labels = raw19671Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19671 raw19671Labels permutation434 hz
    mixedMoment B raw19671step0 raw19671step0Labels = mixedMoment B raw19671step1 raw19671step1Labels := by
      have hz : ∀ j, raw19671step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19671step1 = (fun i j => raw19671step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19671step1 raw19671step0; decide +kernel
      have hl : raw19671step1Labels = raw19671step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19671step0 raw19671step0Labels permutation80 hz
    mixedMoment B raw19671step1 raw19671step1Labels = mixedMoment B raw19671step2 raw19671step2Labels := by
      have ha : raw19671step2 = (fun i j => raw19671step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19671step2 raw19671step1; decide +kernel
      have hl : raw19671step2Labels = raw19671step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19671step1 raw19671step1Labels permutation29 permutation7
    mixedMoment B raw19671step2 raw19671step2Labels = mixedMoment B raw19671step3 raw19671step3Labels := by
      have ha : raw19671step3 = raw19671step2 := by apply Matrix.ext; unfold raw19671step3 raw19671step2; decide +kernel
      have hl : raw19671step2Labels = labelEmbedding1 ∘ raw19671step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19671step2 raw19671step2Labels raw19671step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1692 node1692Labels := by rfl

def raw19672 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19672Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19672step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19672step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19672step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19672step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19672step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![-1, 1, 0], ![-1, 0, 1], ![-1, -3, 4]]
def raw19672step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19672step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![1, -1, 0], ![1, 0, -1], ![1, 3, -4]]
def raw19672step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19672step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![1, -1, 0], ![1, 0, -1], ![1, 3, -4]]
def raw19672step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19672 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19672 raw19672Labels = mixedMoment B node1532 node1532Labels := by
  calc
    mixedMoment B raw19672 raw19672Labels = mixedMoment B raw19672step0 raw19672step0Labels := by
      have hz : ∀ j, raw19672 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19672step0 = (fun i j => raw19672 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19672step0 raw19672; decide +kernel
      have hl : raw19672step0Labels = raw19672Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19672 raw19672Labels permutation434 hz
    mixedMoment B raw19672step0 raw19672step0Labels = mixedMoment B raw19672step1 raw19672step1Labels := by
      have hz : ∀ j, raw19672step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19672step1 = (fun i j => raw19672step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19672step1 raw19672step0; decide +kernel
      have hl : raw19672step1Labels = raw19672step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19672step0 raw19672step0Labels permutation56 hz
    mixedMoment B raw19672step1 raw19672step1Labels = mixedMoment B raw19672step2 raw19672step2Labels := by
      have ha : raw19672step2 = (fun i j => raw19672step1 (permutation10 i) (permutation5 j)) := by apply Matrix.ext; unfold raw19672step2 raw19672step1; decide +kernel
      have hl : raw19672step2Labels = raw19672step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19672step1 raw19672step1Labels permutation10 permutation5
    mixedMoment B raw19672step2 raw19672step2Labels = mixedMoment B raw19672step3 raw19672step3Labels := by
      have ha : raw19672step3 = -raw19672step2 := by apply Matrix.ext; change ∀ i j, raw19672step3 i j = -(raw19672step2 i j); unfold raw19672step3 raw19672step2; decide +kernel
      have hl : raw19672step3Labels = raw19672step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19672step3 raw19672step3Labels = mixedMoment B raw19672step4 raw19672step4Labels := by
      have ha : raw19672step4 = raw19672step3 := by apply Matrix.ext; unfold raw19672step4 raw19672step3; decide +kernel
      have hl : raw19672step3Labels = labelEmbedding1 ∘ raw19672step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19672step3 raw19672step3Labels raw19672step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1532 node1532Labels := by rfl

def raw19673 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19673Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19673step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19673step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19673step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw19673step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19673step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw19673step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19673 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19673 raw19673Labels = mixedMoment B node1672 node1672Labels := by
  calc
    mixedMoment B raw19673 raw19673Labels = mixedMoment B raw19673step0 raw19673step0Labels := by
      have hz : ∀ j, raw19673 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19673step0 = (fun i j => raw19673 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19673step0 raw19673; decide +kernel
      have hl : raw19673step0Labels = raw19673Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19673 raw19673Labels permutation434 hz
    mixedMoment B raw19673step0 raw19673step0Labels = mixedMoment B raw19673step1 raw19673step1Labels := by
      have ha : raw19673step1 = (fun i j => raw19673step0 (permutation143 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19673step1 raw19673step0; decide +kernel
      have hl : raw19673step1Labels = raw19673step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19673step0 raw19673step0Labels permutation143 permutation7
    mixedMoment B raw19673step1 raw19673step1Labels = mixedMoment B raw19673step2 raw19673step2Labels := by
      have ha : raw19673step2 = raw19673step1 := by apply Matrix.ext; unfold raw19673step2 raw19673step1; decide +kernel
      have hl : raw19673step1Labels = labelEmbedding1 ∘ raw19673step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19673step1 raw19673step1Labels raw19673step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1672 node1672Labels := by rfl

def raw19674 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19674Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19674step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19674step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19674step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw19674step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19674step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw19674step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19674 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19674 raw19674Labels = mixedMoment B node1672 node1672Labels := by
  calc
    mixedMoment B raw19674 raw19674Labels = mixedMoment B raw19674step0 raw19674step0Labels := by
      have hz : ∀ j, raw19674 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw19674step0 = (fun i j => raw19674 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw19674step0 raw19674; decide +kernel
      have hl : raw19674step0Labels = raw19674Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19674 raw19674Labels permutation265 hz
    mixedMoment B raw19674step0 raw19674step0Labels = mixedMoment B raw19674step1 raw19674step1Labels := by
      have ha : raw19674step1 = (fun i j => raw19674step0 (permutation137 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19674step1 raw19674step0; decide +kernel
      have hl : raw19674step1Labels = raw19674step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19674step0 raw19674step0Labels permutation137 permutation7
    mixedMoment B raw19674step1 raw19674step1Labels = mixedMoment B raw19674step2 raw19674step2Labels := by
      have ha : raw19674step2 = raw19674step1 := by apply Matrix.ext; unfold raw19674step2 raw19674step1; decide +kernel
      have hl : raw19674step1Labels = labelEmbedding1 ∘ raw19674step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19674step1 raw19674step1Labels raw19674step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1672 node1672Labels := by rfl

def raw19675 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![4, -1, -3]]
def raw19675Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19675step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![4, -1, -3]]
def raw19675step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19675step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 0, 1], ![4, -1, -3]]
def raw19675step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19675step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 0, -1], ![2, 2, -4]]
def raw19675step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19675step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 0, -1], ![2, 2, -4]]
def raw19675step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19675 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19675 raw19675Labels = mixedMoment B node1692 node1692Labels := by
  calc
    mixedMoment B raw19675 raw19675Labels = mixedMoment B raw19675step0 raw19675step0Labels := by
      have hz : ∀ j, raw19675 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19675step0 = (fun i j => raw19675 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19675step0 raw19675; decide +kernel
      have hl : raw19675step0Labels = raw19675Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19675 raw19675Labels permutation434 hz
    mixedMoment B raw19675step0 raw19675step0Labels = mixedMoment B raw19675step1 raw19675step1Labels := by
      have hz : ∀ j, raw19675step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19675step1 = (fun i j => raw19675step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19675step1 raw19675step0; decide +kernel
      have hl : raw19675step1Labels = raw19675step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19675step0 raw19675step0Labels permutation56 hz
    mixedMoment B raw19675step1 raw19675step1Labels = mixedMoment B raw19675step2 raw19675step2Labels := by
      have ha : raw19675step2 = (fun i j => raw19675step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19675step2 raw19675step1; decide +kernel
      have hl : raw19675step2Labels = raw19675step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19675step1 raw19675step1Labels permutation29 permutation7
    mixedMoment B raw19675step2 raw19675step2Labels = mixedMoment B raw19675step3 raw19675step3Labels := by
      have ha : raw19675step3 = raw19675step2 := by apply Matrix.ext; unfold raw19675step3 raw19675step2; decide +kernel
      have hl : raw19675step2Labels = labelEmbedding1 ∘ raw19675step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19675step2 raw19675step2Labels raw19675step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1692 node1692Labels := by rfl

def raw19676 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19676Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19676step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19676step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19676step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19676step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19676step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![-1, 1, 0], ![-1, 0, 1], ![-1, -3, 4]]
def raw19676step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19676step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![1, -1, 0], ![1, 0, -1], ![1, 3, -4]]
def raw19676step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19676step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![1, -1, 0], ![1, 0, -1], ![1, 3, -4]]
def raw19676step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19676 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19676 raw19676Labels = mixedMoment B node1532 node1532Labels := by
  calc
    mixedMoment B raw19676 raw19676Labels = mixedMoment B raw19676step0 raw19676step0Labels := by
      have hz : ∀ j, raw19676 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19676step0 = (fun i j => raw19676 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19676step0 raw19676; decide +kernel
      have hl : raw19676step0Labels = raw19676Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19676 raw19676Labels permutation346 hz
    mixedMoment B raw19676step0 raw19676step0Labels = mixedMoment B raw19676step1 raw19676step1Labels := by
      have hz : ∀ j, raw19676step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19676step1 = (fun i j => raw19676step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19676step1 raw19676step0; decide +kernel
      have hl : raw19676step1Labels = raw19676step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19676step0 raw19676step0Labels permutation56 hz
    mixedMoment B raw19676step1 raw19676step1Labels = mixedMoment B raw19676step2 raw19676step2Labels := by
      have ha : raw19676step2 = (fun i j => raw19676step1 (permutation10 i) (permutation5 j)) := by apply Matrix.ext; unfold raw19676step2 raw19676step1; decide +kernel
      have hl : raw19676step2Labels = raw19676step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19676step1 raw19676step1Labels permutation10 permutation5
    mixedMoment B raw19676step2 raw19676step2Labels = mixedMoment B raw19676step3 raw19676step3Labels := by
      have ha : raw19676step3 = -raw19676step2 := by apply Matrix.ext; change ∀ i j, raw19676step3 i j = -(raw19676step2 i j); unfold raw19676step3 raw19676step2; decide +kernel
      have hl : raw19676step3Labels = raw19676step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19676step3 raw19676step3Labels = mixedMoment B raw19676step4 raw19676step4Labels := by
      have ha : raw19676step4 = raw19676step3 := by apply Matrix.ext; unfold raw19676step4 raw19676step3; decide +kernel
      have hl : raw19676step3Labels = labelEmbedding1 ∘ raw19676step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19676step3 raw19676step3Labels raw19676step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1532 node1532Labels := by rfl

def raw19677 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19677Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19677step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19677step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19677step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw19677step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19677step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw19677step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19677 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19677 raw19677Labels = mixedMoment B node1672 node1672Labels := by
  calc
    mixedMoment B raw19677 raw19677Labels = mixedMoment B raw19677step0 raw19677step0Labels := by
      have hz : ∀ j, raw19677 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19677step0 = (fun i j => raw19677 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19677step0 raw19677; decide +kernel
      have hl : raw19677step0Labels = raw19677Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19677 raw19677Labels permutation346 hz
    mixedMoment B raw19677step0 raw19677step0Labels = mixedMoment B raw19677step1 raw19677step1Labels := by
      have ha : raw19677step1 = (fun i j => raw19677step0 (permutation143 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19677step1 raw19677step0; decide +kernel
      have hl : raw19677step1Labels = raw19677step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19677step0 raw19677step0Labels permutation143 permutation7
    mixedMoment B raw19677step1 raw19677step1Labels = mixedMoment B raw19677step2 raw19677step2Labels := by
      have ha : raw19677step2 = raw19677step1 := by apply Matrix.ext; unfold raw19677step2 raw19677step1; decide +kernel
      have hl : raw19677step1Labels = labelEmbedding1 ∘ raw19677step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19677step1 raw19677step1Labels raw19677step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1672 node1672Labels := by rfl

def raw19678 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19678Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19678step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19678step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19678step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw19678step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19678step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw19678step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19678 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19678 raw19678Labels = mixedMoment B node1672 node1672Labels := by
  calc
    mixedMoment B raw19678 raw19678Labels = mixedMoment B raw19678step0 raw19678step0Labels := by
      have hz : ∀ j, raw19678 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw19678step0 = (fun i j => raw19678 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw19678step0 raw19678; decide +kernel
      have hl : raw19678step0Labels = raw19678Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19678 raw19678Labels permutation265 hz
    mixedMoment B raw19678step0 raw19678step0Labels = mixedMoment B raw19678step1 raw19678step1Labels := by
      have ha : raw19678step1 = (fun i j => raw19678step0 (permutation143 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19678step1 raw19678step0; decide +kernel
      have hl : raw19678step1Labels = raw19678step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19678step0 raw19678step0Labels permutation143 permutation7
    mixedMoment B raw19678step1 raw19678step1Labels = mixedMoment B raw19678step2 raw19678step2Labels := by
      have ha : raw19678step2 = raw19678step1 := by apply Matrix.ext; unfold raw19678step2 raw19678step1; decide +kernel
      have hl : raw19678step1Labels = labelEmbedding1 ∘ raw19678step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19678step1 raw19678step1Labels raw19678step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1672 node1672Labels := by rfl

def raw19679 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![4, -1, -3]]
def raw19679Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19679step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![4, -1, -3]]
def raw19679step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19679step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 0, 1], ![4, -1, -3]]
def raw19679step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19679step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 0, -1], ![2, 2, -4]]
def raw19679step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19679step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 0, -1], ![2, 2, -4]]
def raw19679step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19679 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19679 raw19679Labels = mixedMoment B node1692 node1692Labels := by
  calc
    mixedMoment B raw19679 raw19679Labels = mixedMoment B raw19679step0 raw19679step0Labels := by
      have hz : ∀ j, raw19679 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19679step0 = (fun i j => raw19679 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19679step0 raw19679; decide +kernel
      have hl : raw19679step0Labels = raw19679Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19679 raw19679Labels permutation346 hz
    mixedMoment B raw19679step0 raw19679step0Labels = mixedMoment B raw19679step1 raw19679step1Labels := by
      have hz : ∀ j, raw19679step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19679step1 = (fun i j => raw19679step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19679step1 raw19679step0; decide +kernel
      have hl : raw19679step1Labels = raw19679step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19679step0 raw19679step0Labels permutation56 hz
    mixedMoment B raw19679step1 raw19679step1Labels = mixedMoment B raw19679step2 raw19679step2Labels := by
      have ha : raw19679step2 = (fun i j => raw19679step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19679step2 raw19679step1; decide +kernel
      have hl : raw19679step2Labels = raw19679step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19679step1 raw19679step1Labels permutation29 permutation7
    mixedMoment B raw19679step2 raw19679step2Labels = mixedMoment B raw19679step3 raw19679step3Labels := by
      have ha : raw19679step3 = raw19679step2 := by apply Matrix.ext; unfold raw19679step3 raw19679step2; decide +kernel
      have hl : raw19679step2Labels = labelEmbedding1 ∘ raw19679step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19679step2 raw19679step2Labels raw19679step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1692 node1692Labels := by rfl

def raw19680 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![4, -1, -3]]
def raw19680Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19680step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![4, -1, -3]]
def raw19680step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19680step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -2, 1], ![4, -1, -3]]
def raw19680step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19680step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -2, 1], ![4, -1, -3]]
def raw19680step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19680step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 2, -5], ![-1, -3, 4], ![-2, 1, 1]]
def raw19680step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19680step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![1, 3, -4], ![2, -1, -1]]
def raw19680step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19680step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![1, 3, -4], ![2, -1, -1]]
def raw19680step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19680 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19680 raw19680Labels = mixedMoment B node1540 node1540Labels := by
  calc
    mixedMoment B raw19680 raw19680Labels = mixedMoment B raw19680step0 raw19680step0Labels := by
      have hz : ∀ j, raw19680 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19680step0 = (fun i j => raw19680 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19680step0 raw19680; decide +kernel
      have hl : raw19680step0Labels = raw19680Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19680 raw19680Labels permutation434 hz
    mixedMoment B raw19680step0 raw19680step0Labels = mixedMoment B raw19680step1 raw19680step1Labels := by
      have hz : ∀ j, raw19680step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19680step1 = (fun i j => raw19680step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19680step1 raw19680step0; decide +kernel
      have hl : raw19680step1Labels = raw19680step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19680step0 raw19680step0Labels permutation80 hz
    mixedMoment B raw19680step1 raw19680step1Labels = mixedMoment B raw19680step2 raw19680step2Labels := by
      have hz : ∀ j, raw19680step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19680step2 = (fun i j => raw19680step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19680step2 raw19680step1; decide +kernel
      have hl : raw19680step2Labels = raw19680step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19680step1 raw19680step1Labels permutation14 hz
    mixedMoment B raw19680step2 raw19680step2Labels = mixedMoment B raw19680step3 raw19680step3Labels := by
      have ha : raw19680step3 = (fun i j => raw19680step2 (permutation3 i) (permutation5 j)) := by apply Matrix.ext; unfold raw19680step3 raw19680step2; decide +kernel
      have hl : raw19680step3Labels = raw19680step2Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19680step2 raw19680step2Labels permutation3 permutation5
    mixedMoment B raw19680step3 raw19680step3Labels = mixedMoment B raw19680step4 raw19680step4Labels := by
      have ha : raw19680step4 = -raw19680step3 := by apply Matrix.ext; change ∀ i j, raw19680step4 i j = -(raw19680step3 i j); unfold raw19680step4 raw19680step3; decide +kernel
      have hl : raw19680step4Labels = raw19680step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19680step4 raw19680step4Labels = mixedMoment B raw19680step5 raw19680step5Labels := by
      have ha : raw19680step5 = raw19680step4 := by apply Matrix.ext; unfold raw19680step5 raw19680step4; decide +kernel
      have hl : raw19680step4Labels = labelEmbedding1 ∘ raw19680step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19680step4 raw19680step4Labels raw19680step5Labels labelEmbedding1 hl
    _ = mixedMoment B node1540 node1540Labels := by rfl

def raw19681 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![4, -1, -3]]
def raw19681Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19681step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![4, -1, -3]]
def raw19681step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19681step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -2, 1], ![4, -1, -3]]
def raw19681step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19681step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -2, 1], ![2, 2, -4]]
def raw19681step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19681step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -2, 1], ![2, 2, -4]]
def raw19681step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19681 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19681 raw19681Labels = mixedMoment B node1722 node1722Labels := by
  calc
    mixedMoment B raw19681 raw19681Labels = mixedMoment B raw19681step0 raw19681step0Labels := by
      have hz : ∀ j, raw19681 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19681step0 = (fun i j => raw19681 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19681step0 raw19681; decide +kernel
      have hl : raw19681step0Labels = raw19681Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19681 raw19681Labels permutation434 hz
    mixedMoment B raw19681step0 raw19681step0Labels = mixedMoment B raw19681step1 raw19681step1Labels := by
      have hz : ∀ j, raw19681step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19681step1 = (fun i j => raw19681step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19681step1 raw19681step0; decide +kernel
      have hl : raw19681step1Labels = raw19681step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19681step0 raw19681step0Labels permutation80 hz
    mixedMoment B raw19681step1 raw19681step1Labels = mixedMoment B raw19681step2 raw19681step2Labels := by
      have ha : raw19681step2 = (fun i j => raw19681step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19681step2 raw19681step1; decide +kernel
      have hl : raw19681step2Labels = raw19681step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19681step1 raw19681step1Labels permutation29 permutation7
    mixedMoment B raw19681step2 raw19681step2Labels = mixedMoment B raw19681step3 raw19681step3Labels := by
      have ha : raw19681step3 = raw19681step2 := by apply Matrix.ext; unfold raw19681step3 raw19681step2; decide +kernel
      have hl : raw19681step2Labels = labelEmbedding1 ∘ raw19681step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19681step2 raw19681step2Labels raw19681step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1722 node1722Labels := by rfl

def raw19682 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![4, -1, -3]]
def raw19682Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19682step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![4, -1, -3]]
def raw19682step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19682step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -2, 1], ![4, -1, -3]]
def raw19682step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19682step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -2, 1], ![2, 2, -4]]
def raw19682step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19682step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -2, 1], ![2, 2, -4]]
def raw19682step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19682 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19682 raw19682Labels = mixedMoment B node1722 node1722Labels := by
  calc
    mixedMoment B raw19682 raw19682Labels = mixedMoment B raw19682step0 raw19682step0Labels := by
      have hz : ∀ j, raw19682 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19682step0 = (fun i j => raw19682 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19682step0 raw19682; decide +kernel
      have hl : raw19682step0Labels = raw19682Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19682 raw19682Labels permutation434 hz
    mixedMoment B raw19682step0 raw19682step0Labels = mixedMoment B raw19682step1 raw19682step1Labels := by
      have hz : ∀ j, raw19682step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19682step1 = (fun i j => raw19682step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19682step1 raw19682step0; decide +kernel
      have hl : raw19682step1Labels = raw19682step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19682step0 raw19682step0Labels permutation56 hz
    mixedMoment B raw19682step1 raw19682step1Labels = mixedMoment B raw19682step2 raw19682step2Labels := by
      have ha : raw19682step2 = (fun i j => raw19682step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19682step2 raw19682step1; decide +kernel
      have hl : raw19682step2Labels = raw19682step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19682step1 raw19682step1Labels permutation29 permutation7
    mixedMoment B raw19682step2 raw19682step2Labels = mixedMoment B raw19682step3 raw19682step3Labels := by
      have ha : raw19682step3 = raw19682step2 := by apply Matrix.ext; unfold raw19682step3 raw19682step2; decide +kernel
      have hl : raw19682step2Labels = labelEmbedding1 ∘ raw19682step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19682step2 raw19682step2Labels raw19682step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1722 node1722Labels := by rfl

def raw19683 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![4, -1, -3]]
def raw19683Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19683step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![4, -1, -3]]
def raw19683step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19683step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -2, 1], ![4, -1, -3]]
def raw19683step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19683step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -2, 1], ![2, 2, -4]]
def raw19683step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19683step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -2, 1], ![2, 2, -4]]
def raw19683step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19683 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19683 raw19683Labels = mixedMoment B node1722 node1722Labels := by
  calc
    mixedMoment B raw19683 raw19683Labels = mixedMoment B raw19683step0 raw19683step0Labels := by
      have hz : ∀ j, raw19683 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19683step0 = (fun i j => raw19683 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19683step0 raw19683; decide +kernel
      have hl : raw19683step0Labels = raw19683Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19683 raw19683Labels permutation346 hz
    mixedMoment B raw19683step0 raw19683step0Labels = mixedMoment B raw19683step1 raw19683step1Labels := by
      have hz : ∀ j, raw19683step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19683step1 = (fun i j => raw19683step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19683step1 raw19683step0; decide +kernel
      have hl : raw19683step1Labels = raw19683step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19683step0 raw19683step0Labels permutation56 hz
    mixedMoment B raw19683step1 raw19683step1Labels = mixedMoment B raw19683step2 raw19683step2Labels := by
      have ha : raw19683step2 = (fun i j => raw19683step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19683step2 raw19683step1; decide +kernel
      have hl : raw19683step2Labels = raw19683step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19683step1 raw19683step1Labels permutation29 permutation7
    mixedMoment B raw19683step2 raw19683step2Labels = mixedMoment B raw19683step3 raw19683step3Labels := by
      have ha : raw19683step3 = raw19683step2 := by apply Matrix.ext; unfold raw19683step3 raw19683step2; decide +kernel
      have hl : raw19683step2Labels = labelEmbedding1 ∘ raw19683step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19683step2 raw19683step2Labels raw19683step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1722 node1722Labels := by rfl

def raw19684 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![5, -2, -3]]
def raw19684Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19684step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![5, -2, -3]]
def raw19684step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19684step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, -1, 1], ![5, -2, -3]]
def raw19684step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19684step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![5, -2, -3]]
def raw19684step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19684step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 2, -5], ![-1, 1, 0], ![-2, -3, 5]]
def raw19684step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19684step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![1, -1, 0], ![2, 3, -5]]
def raw19684step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19684step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![1, -1, 0], ![2, 3, -5]]
def raw19684step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19684 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19684 raw19684Labels = mixedMoment B node1534 node1534Labels := by
  calc
    mixedMoment B raw19684 raw19684Labels = mixedMoment B raw19684step0 raw19684step0Labels := by
      have hz : ∀ j, raw19684 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19684step0 = (fun i j => raw19684 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19684step0 raw19684; decide +kernel
      have hl : raw19684step0Labels = raw19684Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19684 raw19684Labels permutation434 hz
    mixedMoment B raw19684step0 raw19684step0Labels = mixedMoment B raw19684step1 raw19684step1Labels := by
      have hz : ∀ j, raw19684step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19684step1 = (fun i j => raw19684step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19684step1 raw19684step0; decide +kernel
      have hl : raw19684step1Labels = raw19684step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19684step0 raw19684step0Labels permutation80 hz
    mixedMoment B raw19684step1 raw19684step1Labels = mixedMoment B raw19684step2 raw19684step2Labels := by
      have hz : ∀ j, raw19684step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19684step2 = (fun i j => raw19684step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19684step2 raw19684step1; decide +kernel
      have hl : raw19684step2Labels = raw19684step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19684step1 raw19684step1Labels permutation14 hz
    mixedMoment B raw19684step2 raw19684step2Labels = mixedMoment B raw19684step3 raw19684step3Labels := by
      have ha : raw19684step3 = (fun i j => raw19684step2 (permutation2 i) (permutation5 j)) := by apply Matrix.ext; unfold raw19684step3 raw19684step2; decide +kernel
      have hl : raw19684step3Labels = raw19684step2Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19684step2 raw19684step2Labels permutation2 permutation5
    mixedMoment B raw19684step3 raw19684step3Labels = mixedMoment B raw19684step4 raw19684step4Labels := by
      have ha : raw19684step4 = -raw19684step3 := by apply Matrix.ext; change ∀ i j, raw19684step4 i j = -(raw19684step3 i j); unfold raw19684step4 raw19684step3; decide +kernel
      have hl : raw19684step4Labels = raw19684step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19684step4 raw19684step4Labels = mixedMoment B raw19684step5 raw19684step5Labels := by
      have ha : raw19684step5 = raw19684step4 := by apply Matrix.ext; unfold raw19684step5 raw19684step4; decide +kernel
      have hl : raw19684step4Labels = labelEmbedding1 ∘ raw19684step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19684step4 raw19684step4Labels raw19684step5Labels labelEmbedding1 hl
    _ = mixedMoment B node1534 node1534Labels := by rfl

def raw19685 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![5, -2, -3]]
def raw19685Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19685step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![5, -2, -3]]
def raw19685step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19685step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![5, -2, -3]]
def raw19685step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19685step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw19685step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19685step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw19685step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19685 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19685 raw19685Labels = mixedMoment B node1516 node1516Labels := by
  calc
    mixedMoment B raw19685 raw19685Labels = mixedMoment B raw19685step0 raw19685step0Labels := by
      have hz : ∀ j, raw19685 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19685step0 = (fun i j => raw19685 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19685step0 raw19685; decide +kernel
      have hl : raw19685step0Labels = raw19685Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19685 raw19685Labels permutation434 hz
    mixedMoment B raw19685step0 raw19685step0Labels = mixedMoment B raw19685step1 raw19685step1Labels := by
      have hz : ∀ j, raw19685step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19685step1 = (fun i j => raw19685step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19685step1 raw19685step0; decide +kernel
      have hl : raw19685step1Labels = raw19685step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19685step0 raw19685step0Labels permutation80 hz
    mixedMoment B raw19685step1 raw19685step1Labels = mixedMoment B raw19685step2 raw19685step2Labels := by
      have ha : raw19685step2 = (fun i j => raw19685step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19685step2 raw19685step1; decide +kernel
      have hl : raw19685step2Labels = raw19685step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19685step1 raw19685step1Labels permutation29 permutation7
    mixedMoment B raw19685step2 raw19685step2Labels = mixedMoment B raw19685step3 raw19685step3Labels := by
      have ha : raw19685step3 = raw19685step2 := by apply Matrix.ext; unfold raw19685step3 raw19685step2; decide +kernel
      have hl : raw19685step2Labels = labelEmbedding1 ∘ raw19685step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19685step2 raw19685step2Labels raw19685step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1516 node1516Labels := by rfl

def raw19686 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![5, -2, -3]]
def raw19686Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19686step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![5, -2, -3]]
def raw19686step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19686step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![5, -2, -3]]
def raw19686step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19686step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw19686step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19686step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw19686step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19686 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19686 raw19686Labels = mixedMoment B node1516 node1516Labels := by
  calc
    mixedMoment B raw19686 raw19686Labels = mixedMoment B raw19686step0 raw19686step0Labels := by
      have hz : ∀ j, raw19686 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19686step0 = (fun i j => raw19686 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19686step0 raw19686; decide +kernel
      have hl : raw19686step0Labels = raw19686Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19686 raw19686Labels permutation434 hz
    mixedMoment B raw19686step0 raw19686step0Labels = mixedMoment B raw19686step1 raw19686step1Labels := by
      have hz : ∀ j, raw19686step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19686step1 = (fun i j => raw19686step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19686step1 raw19686step0; decide +kernel
      have hl : raw19686step1Labels = raw19686step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19686step0 raw19686step0Labels permutation56 hz
    mixedMoment B raw19686step1 raw19686step1Labels = mixedMoment B raw19686step2 raw19686step2Labels := by
      have ha : raw19686step2 = (fun i j => raw19686step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19686step2 raw19686step1; decide +kernel
      have hl : raw19686step2Labels = raw19686step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19686step1 raw19686step1Labels permutation29 permutation7
    mixedMoment B raw19686step2 raw19686step2Labels = mixedMoment B raw19686step3 raw19686step3Labels := by
      have ha : raw19686step3 = raw19686step2 := by apply Matrix.ext; unfold raw19686step3 raw19686step2; decide +kernel
      have hl : raw19686step2Labels = labelEmbedding1 ∘ raw19686step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19686step2 raw19686step2Labels raw19686step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1516 node1516Labels := by rfl

def raw19687 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![5, -2, -3]]
def raw19687Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19687step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![5, -2, -3]]
def raw19687step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19687step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![5, -2, -3]]
def raw19687step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19687step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw19687step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19687step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw19687step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19687 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19687 raw19687Labels = mixedMoment B node1516 node1516Labels := by
  calc
    mixedMoment B raw19687 raw19687Labels = mixedMoment B raw19687step0 raw19687step0Labels := by
      have hz : ∀ j, raw19687 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19687step0 = (fun i j => raw19687 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19687step0 raw19687; decide +kernel
      have hl : raw19687step0Labels = raw19687Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19687 raw19687Labels permutation346 hz
    mixedMoment B raw19687step0 raw19687step0Labels = mixedMoment B raw19687step1 raw19687step1Labels := by
      have hz : ∀ j, raw19687step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19687step1 = (fun i j => raw19687step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19687step1 raw19687step0; decide +kernel
      have hl : raw19687step1Labels = raw19687step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19687step0 raw19687step0Labels permutation56 hz
    mixedMoment B raw19687step1 raw19687step1Labels = mixedMoment B raw19687step2 raw19687step2Labels := by
      have ha : raw19687step2 = (fun i j => raw19687step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19687step2 raw19687step1; decide +kernel
      have hl : raw19687step2Labels = raw19687step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19687step1 raw19687step1Labels permutation29 permutation7
    mixedMoment B raw19687step2 raw19687step2Labels = mixedMoment B raw19687step3 raw19687step3Labels := by
      have ha : raw19687step3 = raw19687step2 := by apply Matrix.ext; unfold raw19687step3 raw19687step2; decide +kernel
      have hl : raw19687step2Labels = labelEmbedding1 ∘ raw19687step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19687step2 raw19687step2Labels raw19687step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1516 node1516Labels := by rfl

def raw19688 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![5, -2, -3]]
def raw19688Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19688step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![5, -2, -3]]
def raw19688step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19688step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 0, 1], ![5, -2, -3]]
def raw19688step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19688step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![5, -2, -3]]
def raw19688step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19688step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![1, 0, -1], ![2, 2, -4]]
def raw19688step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19688step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![1, 0, -1], ![2, 2, -4]]
def raw19688step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19688 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19688 raw19688Labels = mixedMoment B node1537 node1537Labels := by
  calc
    mixedMoment B raw19688 raw19688Labels = mixedMoment B raw19688step0 raw19688step0Labels := by
      have hz : ∀ j, raw19688 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19688step0 = (fun i j => raw19688 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19688step0 raw19688; decide +kernel
      have hl : raw19688step0Labels = raw19688Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19688 raw19688Labels permutation434 hz
    mixedMoment B raw19688step0 raw19688step0Labels = mixedMoment B raw19688step1 raw19688step1Labels := by
      have hz : ∀ j, raw19688step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19688step1 = (fun i j => raw19688step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19688step1 raw19688step0; decide +kernel
      have hl : raw19688step1Labels = raw19688step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19688step0 raw19688step0Labels permutation80 hz
    mixedMoment B raw19688step1 raw19688step1Labels = mixedMoment B raw19688step2 raw19688step2Labels := by
      have hz : ∀ j, raw19688step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19688step2 = (fun i j => raw19688step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19688step2 raw19688step1; decide +kernel
      have hl : raw19688step2Labels = raw19688step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19688step1 raw19688step1Labels permutation14 hz
    mixedMoment B raw19688step2 raw19688step2Labels = mixedMoment B raw19688step3 raw19688step3Labels := by
      have ha : raw19688step3 = (fun i j => raw19688step2 (permutation7 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19688step3 raw19688step2; decide +kernel
      have hl : raw19688step3Labels = raw19688step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19688step2 raw19688step2Labels permutation7 permutation7
    mixedMoment B raw19688step3 raw19688step3Labels = mixedMoment B raw19688step4 raw19688step4Labels := by
      have ha : raw19688step4 = raw19688step3 := by apply Matrix.ext; unfold raw19688step4 raw19688step3; decide +kernel
      have hl : raw19688step3Labels = labelEmbedding1 ∘ raw19688step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19688step3 raw19688step3Labels raw19688step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1537 node1537Labels := by rfl

def raw19689 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19689Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19689step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19689step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19689step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19689step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19689step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw19689step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19689 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19689 raw19689Labels = mixedMoment B node628 node628Labels := by
  calc
    mixedMoment B raw19689 raw19689Labels = mixedMoment B raw19689step0 raw19689step0Labels := by
      have hz : ∀ j, raw19689 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19689step0 = (fun i j => raw19689 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19689step0 raw19689; decide +kernel
      have hl : raw19689step0Labels = raw19689Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19689 raw19689Labels permutation434 hz
    mixedMoment B raw19689step0 raw19689step0Labels = mixedMoment B raw19689step1 raw19689step1Labels := by
      have hz : ∀ j, raw19689step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19689step1 = (fun i j => raw19689step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19689step1 raw19689step0; decide +kernel
      have hl : raw19689step1Labels = raw19689step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19689step0 raw19689step0Labels permutation80 hz
    mixedMoment B raw19689step1 raw19689step1Labels = mixedMoment B raw19689step2 raw19689step2Labels := by
      have ha : raw19689step2 = (fun i j => raw19689step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19689step2 raw19689step1; decide +kernel
      have hl : raw19689step2Labels = raw19689step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19689step1 raw19689step1Labels permutation10 permutation2
    _ = mixedMoment B node628 node628Labels := by rfl

def raw19690 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19690Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19690step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19690step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19690step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19690step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19690step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw19690step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19690 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19690 raw19690Labels = mixedMoment B node628 node628Labels := by
  calc
    mixedMoment B raw19690 raw19690Labels = mixedMoment B raw19690step0 raw19690step0Labels := by
      have hz : ∀ j, raw19690 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19690step0 = (fun i j => raw19690 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19690step0 raw19690; decide +kernel
      have hl : raw19690step0Labels = raw19690Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19690 raw19690Labels permutation434 hz
    mixedMoment B raw19690step0 raw19690step0Labels = mixedMoment B raw19690step1 raw19690step1Labels := by
      have hz : ∀ j, raw19690step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19690step1 = (fun i j => raw19690step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19690step1 raw19690step0; decide +kernel
      have hl : raw19690step1Labels = raw19690step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19690step0 raw19690step0Labels permutation56 hz
    mixedMoment B raw19690step1 raw19690step1Labels = mixedMoment B raw19690step2 raw19690step2Labels := by
      have ha : raw19690step2 = (fun i j => raw19690step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19690step2 raw19690step1; decide +kernel
      have hl : raw19690step2Labels = raw19690step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19690step1 raw19690step1Labels permutation10 permutation2
    _ = mixedMoment B node628 node628Labels := by rfl

def raw19691 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19691Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19691step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19691step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19691step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19691step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19691step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw19691step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19691 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19691 raw19691Labels = mixedMoment B node628 node628Labels := by
  calc
    mixedMoment B raw19691 raw19691Labels = mixedMoment B raw19691step0 raw19691step0Labels := by
      have hz : ∀ j, raw19691 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19691step0 = (fun i j => raw19691 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19691step0 raw19691; decide +kernel
      have hl : raw19691step0Labels = raw19691Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19691 raw19691Labels permutation346 hz
    mixedMoment B raw19691step0 raw19691step0Labels = mixedMoment B raw19691step1 raw19691step1Labels := by
      have hz : ∀ j, raw19691step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19691step1 = (fun i j => raw19691step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19691step1 raw19691step0; decide +kernel
      have hl : raw19691step1Labels = raw19691step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19691step0 raw19691step0Labels permutation56 hz
    mixedMoment B raw19691step1 raw19691step1Labels = mixedMoment B raw19691step2 raw19691step2Labels := by
      have ha : raw19691step2 = (fun i j => raw19691step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19691step2 raw19691step1; decide +kernel
      have hl : raw19691step2Labels = raw19691step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19691step1 raw19691step1Labels permutation10 permutation2
    _ = mixedMoment B node628 node628Labels := by rfl

def raw19692 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![4, -1, -3]]
def raw19692Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19692step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![4, -1, -3]]
def raw19692step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19692step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -2, 1], ![4, -1, -3]]
def raw19692step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19692step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -2, 1], ![4, -1, -3]]
def raw19692step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19692 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19692 raw19692Labels = mixedMoment B node643 node643Labels := by
  calc
    mixedMoment B raw19692 raw19692Labels = mixedMoment B raw19692step0 raw19692step0Labels := by
      have hz : ∀ j, raw19692 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19692step0 = (fun i j => raw19692 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19692step0 raw19692; decide +kernel
      have hl : raw19692step0Labels = raw19692Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19692 raw19692Labels permutation434 hz
    mixedMoment B raw19692step0 raw19692step0Labels = mixedMoment B raw19692step1 raw19692step1Labels := by
      have hz : ∀ j, raw19692step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19692step1 = (fun i j => raw19692step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19692step1 raw19692step0; decide +kernel
      have hl : raw19692step1Labels = raw19692step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19692step0 raw19692step0Labels permutation80 hz
    mixedMoment B raw19692step1 raw19692step1Labels = mixedMoment B raw19692step2 raw19692step2Labels := by
      have hz : ∀ j, raw19692step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19692step2 = (fun i j => raw19692step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19692step2 raw19692step1; decide +kernel
      have hl : raw19692step2Labels = raw19692step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19692step1 raw19692step1Labels permutation14 hz
    _ = mixedMoment B node643 node643Labels := by rfl

def raw19693 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![5, -2, -3]]
def raw19693Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19693step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![5, -2, -3]]
def raw19693step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19693step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, -1, 1], ![5, -2, -3]]
def raw19693step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19693step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![5, -2, -3]]
def raw19693step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19693step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![5, -2, -3], ![0, -1, 1], ![-5, 3, 2]]
def raw19693step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19693step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![5, -3, -2]]
def raw19693step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19693 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19693 raw19693Labels = mixedMoment B node591 node591Labels := by
  calc
    mixedMoment B raw19693 raw19693Labels = mixedMoment B raw19693step0 raw19693step0Labels := by
      have hz : ∀ j, raw19693 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19693step0 = (fun i j => raw19693 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19693step0 raw19693; decide +kernel
      have hl : raw19693step0Labels = raw19693Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19693 raw19693Labels permutation434 hz
    mixedMoment B raw19693step0 raw19693step0Labels = mixedMoment B raw19693step1 raw19693step1Labels := by
      have hz : ∀ j, raw19693step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19693step1 = (fun i j => raw19693step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19693step1 raw19693step0; decide +kernel
      have hl : raw19693step1Labels = raw19693step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19693step0 raw19693step0Labels permutation80 hz
    mixedMoment B raw19693step1 raw19693step1Labels = mixedMoment B raw19693step2 raw19693step2Labels := by
      have hz : ∀ j, raw19693step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19693step2 = (fun i j => raw19693step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19693step2 raw19693step1; decide +kernel
      have hl : raw19693step2Labels = raw19693step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19693step1 raw19693step1Labels permutation14 hz
    mixedMoment B raw19693step2 raw19693step2Labels = mixedMoment B raw19693step3 raw19693step3Labels := by
      have ha : raw19693step3 = (fun i j => raw19693step2 (permutation7 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19693step3 raw19693step2; decide +kernel
      have hl : raw19693step3Labels = raw19693step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19693step2 raw19693step2Labels permutation7 permutation2
    mixedMoment B raw19693step3 raw19693step3Labels = mixedMoment B raw19693step4 raw19693step4Labels := by
      have ha : raw19693step4 = -raw19693step3 := by apply Matrix.ext; change ∀ i j, raw19693step4 i j = -(raw19693step3 i j); unfold raw19693step4 raw19693step3; decide +kernel
      have hl : raw19693step4Labels = raw19693step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node591 node591Labels := by rfl

def raw19694 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19694Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19694step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19694step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19694step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-4, 2, 2]]
def raw19694step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19694step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![4, -2, -2]]
def raw19694step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19694 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19694 raw19694Labels = mixedMoment B node908 node908Labels := by
  calc
    mixedMoment B raw19694 raw19694Labels = mixedMoment B raw19694step0 raw19694step0Labels := by
      have hz : ∀ j, raw19694 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19694step0 = (fun i j => raw19694 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19694step0 raw19694; decide +kernel
      have hl : raw19694step0Labels = raw19694Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19694 raw19694Labels permutation434 hz
    mixedMoment B raw19694step0 raw19694step0Labels = mixedMoment B raw19694step1 raw19694step1Labels := by
      have ha : raw19694step1 = (fun i j => raw19694step0 (permutation139 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19694step1 raw19694step0; decide +kernel
      have hl : raw19694step1Labels = raw19694step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19694step0 raw19694step0Labels permutation139 permutation2
    mixedMoment B raw19694step1 raw19694step1Labels = mixedMoment B raw19694step2 raw19694step2Labels := by
      have ha : raw19694step2 = -raw19694step1 := by apply Matrix.ext; change ∀ i j, raw19694step2 i j = -(raw19694step1 i j); unfold raw19694step2 raw19694step1; decide +kernel
      have hl : raw19694step2Labels = raw19694step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node908 node908Labels := by rfl

def raw19695 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19695Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19695step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19695step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19695step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-4, 2, 2]]
def raw19695step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19695step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![4, -2, -2]]
def raw19695step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19695 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19695 raw19695Labels = mixedMoment B node908 node908Labels := by
  calc
    mixedMoment B raw19695 raw19695Labels = mixedMoment B raw19695step0 raw19695step0Labels := by
      have hz : ∀ j, raw19695 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19695step0 = (fun i j => raw19695 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19695step0 raw19695; decide +kernel
      have hl : raw19695step0Labels = raw19695Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19695 raw19695Labels permutation346 hz
    mixedMoment B raw19695step0 raw19695step0Labels = mixedMoment B raw19695step1 raw19695step1Labels := by
      have ha : raw19695step1 = (fun i j => raw19695step0 (permutation139 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19695step1 raw19695step0; decide +kernel
      have hl : raw19695step1Labels = raw19695step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19695step0 raw19695step0Labels permutation139 permutation2
    mixedMoment B raw19695step1 raw19695step1Labels = mixedMoment B raw19695step2 raw19695step2Labels := by
      have ha : raw19695step2 = -raw19695step1 := by apply Matrix.ext; change ∀ i j, raw19695step2 i j = -(raw19695step1 i j); unfold raw19695step2 raw19695step1; decide +kernel
      have hl : raw19695step2Labels = raw19695step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node908 node908Labels := by rfl

def raw19696 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![4, -1, -3]]
def raw19696Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19696step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![4, -1, -3]]
def raw19696step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19696step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 0, 1], ![4, -1, -3]]
def raw19696step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19696step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![-1, 0, 1], ![-4, 2, 2]]
def raw19696step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19696step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![4, -2, -2]]
def raw19696step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19696 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19696 raw19696Labels = mixedMoment B node934 node934Labels := by
  calc
    mixedMoment B raw19696 raw19696Labels = mixedMoment B raw19696step0 raw19696step0Labels := by
      have hz : ∀ j, raw19696 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19696step0 = (fun i j => raw19696 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19696step0 raw19696; decide +kernel
      have hl : raw19696step0Labels = raw19696Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19696 raw19696Labels permutation434 hz
    mixedMoment B raw19696step0 raw19696step0Labels = mixedMoment B raw19696step1 raw19696step1Labels := by
      have hz : ∀ j, raw19696step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19696step1 = (fun i j => raw19696step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19696step1 raw19696step0; decide +kernel
      have hl : raw19696step1Labels = raw19696step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19696step0 raw19696step0Labels permutation80 hz
    mixedMoment B raw19696step1 raw19696step1Labels = mixedMoment B raw19696step2 raw19696step2Labels := by
      have ha : raw19696step2 = (fun i j => raw19696step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19696step2 raw19696step1; decide +kernel
      have hl : raw19696step2Labels = raw19696step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19696step1 raw19696step1Labels permutation29 permutation2
    mixedMoment B raw19696step2 raw19696step2Labels = mixedMoment B raw19696step3 raw19696step3Labels := by
      have ha : raw19696step3 = -raw19696step2 := by apply Matrix.ext; change ∀ i j, raw19696step3 i j = -(raw19696step2 i j); unfold raw19696step3 raw19696step2; decide +kernel
      have hl : raw19696step3Labels = raw19696step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node934 node934Labels := by rfl

def raw19697 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19697Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19697step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19697step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19697step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-4, 2, 2]]
def raw19697step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19697step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![4, -2, -2]]
def raw19697step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19697 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19697 raw19697Labels = mixedMoment B node908 node908Labels := by
  calc
    mixedMoment B raw19697 raw19697Labels = mixedMoment B raw19697step0 raw19697step0Labels := by
      have hz : ∀ j, raw19697 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19697step0 = (fun i j => raw19697 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19697step0 raw19697; decide +kernel
      have hl : raw19697step0Labels = raw19697Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19697 raw19697Labels permutation434 hz
    mixedMoment B raw19697step0 raw19697step0Labels = mixedMoment B raw19697step1 raw19697step1Labels := by
      have ha : raw19697step1 = (fun i j => raw19697step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19697step1 raw19697step0; decide +kernel
      have hl : raw19697step1Labels = raw19697step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19697step0 raw19697step0Labels permutation145 permutation2
    mixedMoment B raw19697step1 raw19697step1Labels = mixedMoment B raw19697step2 raw19697step2Labels := by
      have ha : raw19697step2 = -raw19697step1 := by apply Matrix.ext; change ∀ i j, raw19697step2 i j = -(raw19697step1 i j); unfold raw19697step2 raw19697step1; decide +kernel
      have hl : raw19697step2Labels = raw19697step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node908 node908Labels := by rfl

def raw19698 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19698Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19698step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19698step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19698step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-4, 2, 2]]
def raw19698step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19698step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![4, -2, -2]]
def raw19698step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19698 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19698 raw19698Labels = mixedMoment B node908 node908Labels := by
  calc
    mixedMoment B raw19698 raw19698Labels = mixedMoment B raw19698step0 raw19698step0Labels := by
      have hz : ∀ j, raw19698 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19698step0 = (fun i j => raw19698 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19698step0 raw19698; decide +kernel
      have hl : raw19698step0Labels = raw19698Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19698 raw19698Labels permutation346 hz
    mixedMoment B raw19698step0 raw19698step0Labels = mixedMoment B raw19698step1 raw19698step1Labels := by
      have ha : raw19698step1 = (fun i j => raw19698step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19698step1 raw19698step0; decide +kernel
      have hl : raw19698step1Labels = raw19698step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19698step0 raw19698step0Labels permutation145 permutation2
    mixedMoment B raw19698step1 raw19698step1Labels = mixedMoment B raw19698step2 raw19698step2Labels := by
      have ha : raw19698step2 = -raw19698step1 := by apply Matrix.ext; change ∀ i j, raw19698step2 i j = -(raw19698step1 i j); unfold raw19698step2 raw19698step1; decide +kernel
      have hl : raw19698step2Labels = raw19698step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node908 node908Labels := by rfl

def raw19699 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![4, -1, -3]]
def raw19699Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19699step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![4, -1, -3]]
def raw19699step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19699step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -2, 1], ![4, -1, -3]]
def raw19699step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19699step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![1, -2, 1], ![-1, 1, 0], ![-4, 2, 2]]
def raw19699step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19699step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![4, -2, -2]]
def raw19699step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19699 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19699 raw19699Labels = mixedMoment B node948 node948Labels := by
  calc
    mixedMoment B raw19699 raw19699Labels = mixedMoment B raw19699step0 raw19699step0Labels := by
      have hz : ∀ j, raw19699 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19699step0 = (fun i j => raw19699 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19699step0 raw19699; decide +kernel
      have hl : raw19699step0Labels = raw19699Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19699 raw19699Labels permutation434 hz
    mixedMoment B raw19699step0 raw19699step0Labels = mixedMoment B raw19699step1 raw19699step1Labels := by
      have hz : ∀ j, raw19699step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19699step1 = (fun i j => raw19699step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19699step1 raw19699step0; decide +kernel
      have hl : raw19699step1Labels = raw19699step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19699step0 raw19699step0Labels permutation80 hz
    mixedMoment B raw19699step1 raw19699step1Labels = mixedMoment B raw19699step2 raw19699step2Labels := by
      have ha : raw19699step2 = (fun i j => raw19699step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19699step2 raw19699step1; decide +kernel
      have hl : raw19699step2Labels = raw19699step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19699step1 raw19699step1Labels permutation31 permutation2
    mixedMoment B raw19699step2 raw19699step2Labels = mixedMoment B raw19699step3 raw19699step3Labels := by
      have ha : raw19699step3 = -raw19699step2 := by apply Matrix.ext; change ∀ i j, raw19699step3 i j = -(raw19699step2 i j); unfold raw19699step3 raw19699step2; decide +kernel
      have hl : raw19699step3Labels = raw19699step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node948 node948Labels := by rfl

def raw19700 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![5, -2, -3]]
def raw19700Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19700step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![5, -2, -3]]
def raw19700step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19700step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![5, -2, -3]]
def raw19700step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19700step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![5, -2, -3], ![0, -1, 1], ![-1, 1, 0], ![-4, 2, 2]]
def raw19700step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19700step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![4, -2, -2]]
def raw19700step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19700 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19700 raw19700Labels = mixedMoment B node584 node584Labels := by
  calc
    mixedMoment B raw19700 raw19700Labels = mixedMoment B raw19700step0 raw19700step0Labels := by
      have hz : ∀ j, raw19700 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19700step0 = (fun i j => raw19700 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19700step0 raw19700; decide +kernel
      have hl : raw19700step0Labels = raw19700Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19700 raw19700Labels permutation434 hz
    mixedMoment B raw19700step0 raw19700step0Labels = mixedMoment B raw19700step1 raw19700step1Labels := by
      have hz : ∀ j, raw19700step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19700step1 = (fun i j => raw19700step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19700step1 raw19700step0; decide +kernel
      have hl : raw19700step1Labels = raw19700step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19700step0 raw19700step0Labels permutation80 hz
    mixedMoment B raw19700step1 raw19700step1Labels = mixedMoment B raw19700step2 raw19700step2Labels := by
      have ha : raw19700step2 = (fun i j => raw19700step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19700step2 raw19700step1; decide +kernel
      have hl : raw19700step2Labels = raw19700step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19700step1 raw19700step1Labels permutation31 permutation2
    mixedMoment B raw19700step2 raw19700step2Labels = mixedMoment B raw19700step3 raw19700step3Labels := by
      have ha : raw19700step3 = -raw19700step2 := by apply Matrix.ext; change ∀ i j, raw19700step3 i j = -(raw19700step2 i j); unfold raw19700step3 raw19700step2; decide +kernel
      have hl : raw19700step3Labels = raw19700step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node584 node584Labels := by rfl

def raw19701 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![4, -1, -3]]
def raw19701Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19701step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![4, -1, -3]]
def raw19701step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19701step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -2, 1], ![4, -1, -3]]
def raw19701step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19701step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![1, -2, 1], ![-1, 1, 0], ![-4, 2, 2]]
def raw19701step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19701step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![4, -2, -2]]
def raw19701step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19701 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19701 raw19701Labels = mixedMoment B node948 node948Labels := by
  calc
    mixedMoment B raw19701 raw19701Labels = mixedMoment B raw19701step0 raw19701step0Labels := by
      have hz : ∀ j, raw19701 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19701step0 = (fun i j => raw19701 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19701step0 raw19701; decide +kernel
      have hl : raw19701step0Labels = raw19701Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19701 raw19701Labels permutation434 hz
    mixedMoment B raw19701step0 raw19701step0Labels = mixedMoment B raw19701step1 raw19701step1Labels := by
      have hz : ∀ j, raw19701step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19701step1 = (fun i j => raw19701step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19701step1 raw19701step0; decide +kernel
      have hl : raw19701step1Labels = raw19701step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19701step0 raw19701step0Labels permutation56 hz
    mixedMoment B raw19701step1 raw19701step1Labels = mixedMoment B raw19701step2 raw19701step2Labels := by
      have ha : raw19701step2 = (fun i j => raw19701step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19701step2 raw19701step1; decide +kernel
      have hl : raw19701step2Labels = raw19701step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19701step1 raw19701step1Labels permutation31 permutation2
    mixedMoment B raw19701step2 raw19701step2Labels = mixedMoment B raw19701step3 raw19701step3Labels := by
      have ha : raw19701step3 = -raw19701step2 := by apply Matrix.ext; change ∀ i j, raw19701step3 i j = -(raw19701step2 i j); unfold raw19701step3 raw19701step2; decide +kernel
      have hl : raw19701step3Labels = raw19701step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node948 node948Labels := by rfl

def raw19702 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![4, -1, -3]]
def raw19702Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19702step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![4, -1, -3]]
def raw19702step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19702step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -2, 1], ![4, -1, -3]]
def raw19702step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19702step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![1, -2, 1], ![-1, 1, 0], ![-4, 2, 2]]
def raw19702step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19702step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![4, -2, -2]]
def raw19702step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19702 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19702 raw19702Labels = mixedMoment B node948 node948Labels := by
  calc
    mixedMoment B raw19702 raw19702Labels = mixedMoment B raw19702step0 raw19702step0Labels := by
      have hz : ∀ j, raw19702 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19702step0 = (fun i j => raw19702 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19702step0 raw19702; decide +kernel
      have hl : raw19702step0Labels = raw19702Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19702 raw19702Labels permutation346 hz
    mixedMoment B raw19702step0 raw19702step0Labels = mixedMoment B raw19702step1 raw19702step1Labels := by
      have hz : ∀ j, raw19702step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19702step1 = (fun i j => raw19702step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19702step1 raw19702step0; decide +kernel
      have hl : raw19702step1Labels = raw19702step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19702step0 raw19702step0Labels permutation56 hz
    mixedMoment B raw19702step1 raw19702step1Labels = mixedMoment B raw19702step2 raw19702step2Labels := by
      have ha : raw19702step2 = (fun i j => raw19702step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19702step2 raw19702step1; decide +kernel
      have hl : raw19702step2Labels = raw19702step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19702step1 raw19702step1Labels permutation31 permutation2
    mixedMoment B raw19702step2 raw19702step2Labels = mixedMoment B raw19702step3 raw19702step3Labels := by
      have ha : raw19702step3 = -raw19702step2 := by apply Matrix.ext; change ∀ i j, raw19702step3 i j = -(raw19702step2 i j); unfold raw19702step3 raw19702step2; decide +kernel
      have hl : raw19702step3Labels = raw19702step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node948 node948Labels := by rfl

def raw19703 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![4, -1, -3]]
def raw19703Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19703step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![4, -1, -3]]
def raw19703step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19703step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 0, 1], ![4, -1, -3]]
def raw19703step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19703step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![4, -1, -3]]
def raw19703step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19703step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, -1, -3], ![-1, 0, 1], ![-3, 1, 2]]
def raw19703step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19703step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![3, -1, -2]]
def raw19703step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19703 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19703 raw19703Labels = mixedMoment B node1089 node1089Labels := by
  calc
    mixedMoment B raw19703 raw19703Labels = mixedMoment B raw19703step0 raw19703step0Labels := by
      have hz : ∀ j, raw19703 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19703step0 = (fun i j => raw19703 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19703step0 raw19703; decide +kernel
      have hl : raw19703step0Labels = raw19703Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19703 raw19703Labels permutation434 hz
    mixedMoment B raw19703step0 raw19703step0Labels = mixedMoment B raw19703step1 raw19703step1Labels := by
      have hz : ∀ j, raw19703step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19703step1 = (fun i j => raw19703step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19703step1 raw19703step0; decide +kernel
      have hl : raw19703step1Labels = raw19703step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19703step0 raw19703step0Labels permutation80 hz
    mixedMoment B raw19703step1 raw19703step1Labels = mixedMoment B raw19703step2 raw19703step2Labels := by
      have hz : ∀ j, raw19703step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19703step2 = (fun i j => raw19703step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19703step2 raw19703step1; decide +kernel
      have hl : raw19703step2Labels = raw19703step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19703step1 raw19703step1Labels permutation14 hz
    mixedMoment B raw19703step2 raw19703step2Labels = mixedMoment B raw19703step3 raw19703step3Labels := by
      have ha : raw19703step3 = (fun i j => raw19703step2 (permutation7 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19703step3 raw19703step2; decide +kernel
      have hl : raw19703step3Labels = raw19703step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19703step2 raw19703step2Labels permutation7 permutation2
    mixedMoment B raw19703step3 raw19703step3Labels = mixedMoment B raw19703step4 raw19703step4Labels := by
      have ha : raw19703step4 = -raw19703step3 := by apply Matrix.ext; change ∀ i j, raw19703step4 i j = -(raw19703step3 i j); unfold raw19703step4 raw19703step3; decide +kernel
      have hl : raw19703step4Labels = raw19703step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1089 node1089Labels := by rfl

def raw19704 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![4, -1, -3]]
def raw19704Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19704step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![4, -1, -3]]
def raw19704step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19704step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 0, 1], ![4, -1, -3]]
def raw19704step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19704step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![-1, 0, 1], ![-4, 2, 2]]
def raw19704step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19704step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![4, -2, -2]]
def raw19704step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19704 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19704 raw19704Labels = mixedMoment B node934 node934Labels := by
  calc
    mixedMoment B raw19704 raw19704Labels = mixedMoment B raw19704step0 raw19704step0Labels := by
      have hz : ∀ j, raw19704 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19704step0 = (fun i j => raw19704 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19704step0 raw19704; decide +kernel
      have hl : raw19704step0Labels = raw19704Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19704 raw19704Labels permutation434 hz
    mixedMoment B raw19704step0 raw19704step0Labels = mixedMoment B raw19704step1 raw19704step1Labels := by
      have hz : ∀ j, raw19704step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19704step1 = (fun i j => raw19704step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19704step1 raw19704step0; decide +kernel
      have hl : raw19704step1Labels = raw19704step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19704step0 raw19704step0Labels permutation56 hz
    mixedMoment B raw19704step1 raw19704step1Labels = mixedMoment B raw19704step2 raw19704step2Labels := by
      have ha : raw19704step2 = (fun i j => raw19704step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19704step2 raw19704step1; decide +kernel
      have hl : raw19704step2Labels = raw19704step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19704step1 raw19704step1Labels permutation29 permutation2
    mixedMoment B raw19704step2 raw19704step2Labels = mixedMoment B raw19704step3 raw19704step3Labels := by
      have ha : raw19704step3 = -raw19704step2 := by apply Matrix.ext; change ∀ i j, raw19704step3 i j = -(raw19704step2 i j); unfold raw19704step3 raw19704step2; decide +kernel
      have hl : raw19704step3Labels = raw19704step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node934 node934Labels := by rfl

def raw19705 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![4, -1, -3]]
def raw19705Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19705step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![4, -1, -3]]
def raw19705step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19705step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 0, 1], ![4, -1, -3]]
def raw19705step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19705step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![-1, 0, 1], ![-4, 2, 2]]
def raw19705step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19705step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![4, -2, -2]]
def raw19705step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19705 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19705 raw19705Labels = mixedMoment B node934 node934Labels := by
  calc
    mixedMoment B raw19705 raw19705Labels = mixedMoment B raw19705step0 raw19705step0Labels := by
      have hz : ∀ j, raw19705 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19705step0 = (fun i j => raw19705 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19705step0 raw19705; decide +kernel
      have hl : raw19705step0Labels = raw19705Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19705 raw19705Labels permutation346 hz
    mixedMoment B raw19705step0 raw19705step0Labels = mixedMoment B raw19705step1 raw19705step1Labels := by
      have hz : ∀ j, raw19705step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19705step1 = (fun i j => raw19705step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19705step1 raw19705step0; decide +kernel
      have hl : raw19705step1Labels = raw19705step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19705step0 raw19705step0Labels permutation56 hz
    mixedMoment B raw19705step1 raw19705step1Labels = mixedMoment B raw19705step2 raw19705step2Labels := by
      have ha : raw19705step2 = (fun i j => raw19705step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19705step2 raw19705step1; decide +kernel
      have hl : raw19705step2Labels = raw19705step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19705step1 raw19705step1Labels permutation29 permutation2
    mixedMoment B raw19705step2 raw19705step2Labels = mixedMoment B raw19705step3 raw19705step3Labels := by
      have ha : raw19705step3 = -raw19705step2 := by apply Matrix.ext; change ∀ i j, raw19705step3 i j = -(raw19705step2 i j); unfold raw19705step3 raw19705step2; decide +kernel
      have hl : raw19705step3Labels = raw19705step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node934 node934Labels := by rfl

def raw19706 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![5, -2, -3]]
def raw19706Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19706step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![5, -2, -3]]
def raw19706step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19706step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 0, 1], ![5, -2, -3]]
def raw19706step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19706step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![5, -2, -3]]
def raw19706step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19706step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![5, -2, -3], ![-1, 0, 1], ![-4, 2, 2]]
def raw19706step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19706step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![4, -2, -2]]
def raw19706step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19706 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19706 raw19706Labels = mixedMoment B node615 node615Labels := by
  calc
    mixedMoment B raw19706 raw19706Labels = mixedMoment B raw19706step0 raw19706step0Labels := by
      have hz : ∀ j, raw19706 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19706step0 = (fun i j => raw19706 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19706step0 raw19706; decide +kernel
      have hl : raw19706step0Labels = raw19706Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19706 raw19706Labels permutation434 hz
    mixedMoment B raw19706step0 raw19706step0Labels = mixedMoment B raw19706step1 raw19706step1Labels := by
      have hz : ∀ j, raw19706step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19706step1 = (fun i j => raw19706step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19706step1 raw19706step0; decide +kernel
      have hl : raw19706step1Labels = raw19706step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19706step0 raw19706step0Labels permutation80 hz
    mixedMoment B raw19706step1 raw19706step1Labels = mixedMoment B raw19706step2 raw19706step2Labels := by
      have hz : ∀ j, raw19706step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19706step2 = (fun i j => raw19706step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19706step2 raw19706step1; decide +kernel
      have hl : raw19706step2Labels = raw19706step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19706step1 raw19706step1Labels permutation14 hz
    mixedMoment B raw19706step2 raw19706step2Labels = mixedMoment B raw19706step3 raw19706step3Labels := by
      have ha : raw19706step3 = (fun i j => raw19706step2 (permutation7 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19706step3 raw19706step2; decide +kernel
      have hl : raw19706step3Labels = raw19706step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19706step2 raw19706step2Labels permutation7 permutation2
    mixedMoment B raw19706step3 raw19706step3Labels = mixedMoment B raw19706step4 raw19706step4Labels := by
      have ha : raw19706step4 = -raw19706step3 := by apply Matrix.ext; change ∀ i j, raw19706step4 i j = -(raw19706step3 i j); unfold raw19706step4 raw19706step3; decide +kernel
      have hl : raw19706step4Labels = raw19706step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node615 node615Labels := by rfl

def raw19707 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![4, -3, -1]]
def raw19707Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19707step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![4, -3, -1]]
def raw19707step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19707step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 1, -1], ![4, -3, -1]]
def raw19707step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19707step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![4, -1, -3]]
def raw19707step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19707step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![4, -1, -3]]
def raw19707step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19707 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19707 raw19707Labels = mixedMoment B node4146 node4146Labels := by
  calc
    mixedMoment B raw19707 raw19707Labels = mixedMoment B raw19707step0 raw19707step0Labels := by
      have hz : ∀ j, raw19707 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19707step0 = (fun i j => raw19707 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19707step0 raw19707; decide +kernel
      have hl : raw19707step0Labels = raw19707Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19707 raw19707Labels permutation434 hz
    mixedMoment B raw19707step0 raw19707step0Labels = mixedMoment B raw19707step1 raw19707step1Labels := by
      have hz : ∀ j, raw19707step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19707step1 = (fun i j => raw19707step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19707step1 raw19707step0; decide +kernel
      have hl : raw19707step1Labels = raw19707step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19707step0 raw19707step0Labels permutation80 hz
    mixedMoment B raw19707step1 raw19707step1Labels = mixedMoment B raw19707step2 raw19707step2Labels := by
      have ha : raw19707step2 = (fun i j => raw19707step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19707step2 raw19707step1; decide +kernel
      have hl : raw19707step2Labels = raw19707step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19707step1 raw19707step1Labels permutation10 permutation3
    mixedMoment B raw19707step2 raw19707step2Labels = mixedMoment B raw19707step3 raw19707step3Labels := by
      have ha : raw19707step3 = raw19707step2 := by apply Matrix.ext; unfold raw19707step3 raw19707step2; decide +kernel
      have hl : raw19707step2Labels = labelEmbedding6 ∘ raw19707step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19707step2 raw19707step2Labels raw19707step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4146 node4146Labels := by rfl

def raw19708 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![4, -3, -1]]
def raw19708Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19708step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 1, -1], ![4, -3, -1]]
def raw19708step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19708step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-4, 2, 2]]
def raw19708step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19708step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![4, -2, -2]]
def raw19708step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19708step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![4, -2, -2]]
def raw19708step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19708 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19708 raw19708Labels = mixedMoment B node4293 node4293Labels := by
  calc
    mixedMoment B raw19708 raw19708Labels = mixedMoment B raw19708step0 raw19708step0Labels := by
      have hz : ∀ j, raw19708 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19708step0 = (fun i j => raw19708 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19708step0 raw19708; decide +kernel
      have hl : raw19708step0Labels = raw19708Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19708 raw19708Labels permutation434 hz
    mixedMoment B raw19708step0 raw19708step0Labels = mixedMoment B raw19708step1 raw19708step1Labels := by
      have ha : raw19708step1 = (fun i j => raw19708step0 (permutation139 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19708step1 raw19708step0; decide +kernel
      have hl : raw19708step1Labels = raw19708step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19708step0 raw19708step0Labels permutation139 permutation3
    mixedMoment B raw19708step1 raw19708step1Labels = mixedMoment B raw19708step2 raw19708step2Labels := by
      have ha : raw19708step2 = -raw19708step1 := by apply Matrix.ext; change ∀ i j, raw19708step2 i j = -(raw19708step1 i j); unfold raw19708step2 raw19708step1; decide +kernel
      have hl : raw19708step2Labels = raw19708step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19708step2 raw19708step2Labels = mixedMoment B raw19708step3 raw19708step3Labels := by
      have ha : raw19708step3 = raw19708step2 := by apply Matrix.ext; unfold raw19708step3 raw19708step2; decide +kernel
      have hl : raw19708step2Labels = labelEmbedding6 ∘ raw19708step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19708step2 raw19708step2Labels raw19708step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4293 node4293Labels := by rfl

def raw19709 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![4, -3, -1]]
def raw19709Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19709step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 1, -1], ![4, -3, -1]]
def raw19709step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19709step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-4, 2, 2]]
def raw19709step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19709step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![4, -2, -2]]
def raw19709step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19709step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![4, -2, -2]]
def raw19709step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19709 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19709 raw19709Labels = mixedMoment B node4293 node4293Labels := by
  calc
    mixedMoment B raw19709 raw19709Labels = mixedMoment B raw19709step0 raw19709step0Labels := by
      have hz : ∀ j, raw19709 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19709step0 = (fun i j => raw19709 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19709step0 raw19709; decide +kernel
      have hl : raw19709step0Labels = raw19709Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19709 raw19709Labels permutation346 hz
    mixedMoment B raw19709step0 raw19709step0Labels = mixedMoment B raw19709step1 raw19709step1Labels := by
      have ha : raw19709step1 = (fun i j => raw19709step0 (permutation139 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19709step1 raw19709step0; decide +kernel
      have hl : raw19709step1Labels = raw19709step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19709step0 raw19709step0Labels permutation139 permutation3
    mixedMoment B raw19709step1 raw19709step1Labels = mixedMoment B raw19709step2 raw19709step2Labels := by
      have ha : raw19709step2 = -raw19709step1 := by apply Matrix.ext; change ∀ i j, raw19709step2 i j = -(raw19709step1 i j); unfold raw19709step2 raw19709step1; decide +kernel
      have hl : raw19709step2Labels = raw19709step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19709step2 raw19709step2Labels = mixedMoment B raw19709step3 raw19709step3Labels := by
      have ha : raw19709step3 = raw19709step2 := by apply Matrix.ext; unfold raw19709step3 raw19709step2; decide +kernel
      have hl : raw19709step2Labels = labelEmbedding6 ∘ raw19709step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19709step2 raw19709step2Labels raw19709step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4293 node4293Labels := by rfl

def raw19710 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![4, -3, -1]]
def raw19710Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19710step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 2, -1], ![4, -3, -1]]
def raw19710step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19710step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 2, -1], ![4, -3, -1]]
def raw19710step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19710step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![1, 0, -1], ![-1, -1, 2], ![-4, 2, 2]]
def raw19710step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19710step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 1, -2], ![4, -2, -2]]
def raw19710step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19710step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 1, -2], ![4, -2, -2]]
def raw19710step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19710 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19710 raw19710Labels = mixedMoment B node4315 node4315Labels := by
  calc
    mixedMoment B raw19710 raw19710Labels = mixedMoment B raw19710step0 raw19710step0Labels := by
      have hz : ∀ j, raw19710 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19710step0 = (fun i j => raw19710 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19710step0 raw19710; decide +kernel
      have hl : raw19710step0Labels = raw19710Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19710 raw19710Labels permutation434 hz
    mixedMoment B raw19710step0 raw19710step0Labels = mixedMoment B raw19710step1 raw19710step1Labels := by
      have hz : ∀ j, raw19710step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19710step1 = (fun i j => raw19710step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19710step1 raw19710step0; decide +kernel
      have hl : raw19710step1Labels = raw19710step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19710step0 raw19710step0Labels permutation80 hz
    mixedMoment B raw19710step1 raw19710step1Labels = mixedMoment B raw19710step2 raw19710step2Labels := by
      have ha : raw19710step2 = (fun i j => raw19710step1 (permutation29 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19710step2 raw19710step1; decide +kernel
      have hl : raw19710step2Labels = raw19710step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19710step1 raw19710step1Labels permutation29 permutation3
    mixedMoment B raw19710step2 raw19710step2Labels = mixedMoment B raw19710step3 raw19710step3Labels := by
      have ha : raw19710step3 = -raw19710step2 := by apply Matrix.ext; change ∀ i j, raw19710step3 i j = -(raw19710step2 i j); unfold raw19710step3 raw19710step2; decide +kernel
      have hl : raw19710step3Labels = raw19710step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19710step3 raw19710step3Labels = mixedMoment B raw19710step4 raw19710step4Labels := by
      have ha : raw19710step4 = raw19710step3 := by apply Matrix.ext; unfold raw19710step4 raw19710step3; decide +kernel
      have hl : raw19710step3Labels = labelEmbedding6 ∘ raw19710step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19710step3 raw19710step3Labels raw19710step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4315 node4315Labels := by rfl

def raw19711 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![4, -3, -1]]
def raw19711Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19711step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![4, -3, -1]]
def raw19711step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19711step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 1, -1], ![4, -3, -1]]
def raw19711step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19711step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![4, -1, -3]]
def raw19711step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19711step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![4, -1, -3]]
def raw19711step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19711 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19711 raw19711Labels = mixedMoment B node4146 node4146Labels := by
  calc
    mixedMoment B raw19711 raw19711Labels = mixedMoment B raw19711step0 raw19711step0Labels := by
      have hz : ∀ j, raw19711 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19711step0 = (fun i j => raw19711 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19711step0 raw19711; decide +kernel
      have hl : raw19711step0Labels = raw19711Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19711 raw19711Labels permutation434 hz
    mixedMoment B raw19711step0 raw19711step0Labels = mixedMoment B raw19711step1 raw19711step1Labels := by
      have hz : ∀ j, raw19711step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19711step1 = (fun i j => raw19711step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19711step1 raw19711step0; decide +kernel
      have hl : raw19711step1Labels = raw19711step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19711step0 raw19711step0Labels permutation56 hz
    mixedMoment B raw19711step1 raw19711step1Labels = mixedMoment B raw19711step2 raw19711step2Labels := by
      have ha : raw19711step2 = (fun i j => raw19711step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19711step2 raw19711step1; decide +kernel
      have hl : raw19711step2Labels = raw19711step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19711step1 raw19711step1Labels permutation10 permutation3
    mixedMoment B raw19711step2 raw19711step2Labels = mixedMoment B raw19711step3 raw19711step3Labels := by
      have ha : raw19711step3 = raw19711step2 := by apply Matrix.ext; unfold raw19711step3 raw19711step2; decide +kernel
      have hl : raw19711step2Labels = labelEmbedding6 ∘ raw19711step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19711step2 raw19711step2Labels raw19711step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4146 node4146Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
