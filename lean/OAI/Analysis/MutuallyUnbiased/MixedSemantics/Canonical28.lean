import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes12
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes13
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes30
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes49
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes74
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes76

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw3584 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw3584Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3584step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw3584step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3584step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw3584step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3584step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -2, 1], ![3, 0, -3]]
def raw3584step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3584 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3584 raw3584Labels = mixedMoment B node1408 node1408Labels := by
  calc
    mixedMoment B raw3584 raw3584Labels = mixedMoment B raw3584step0 raw3584step0Labels := by
      have hz : ∀ j, raw3584 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3584step0 = (fun i j => raw3584 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3584step0 raw3584; decide +kernel
      have hl : raw3584step0Labels = raw3584Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3584 raw3584Labels permutation346 hz
    mixedMoment B raw3584step0 raw3584step0Labels = mixedMoment B raw3584step1 raw3584step1Labels := by
      have hz : ∀ j, raw3584step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3584step1 = (fun i j => raw3584step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3584step1 raw3584step0; decide +kernel
      have hl : raw3584step1Labels = raw3584step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3584step0 raw3584step0Labels permutation56 hz
    mixedMoment B raw3584step1 raw3584step1Labels = mixedMoment B raw3584step2 raw3584step2Labels := by
      have ha : raw3584step2 = (fun i j => raw3584step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3584step2 raw3584step1; decide +kernel
      have hl : raw3584step2Labels = raw3584step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3584step1 raw3584step1Labels permutation8 permutation3
    _ = mixedMoment B node1408 node1408Labels := by rfl

def raw3585 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw3585Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3585step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw3585step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3585step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![-3, 3, 0]]
def raw3585step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3585step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw3585step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3585 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3585 raw3585Labels = mixedMoment B node2092 node2092Labels := by
  calc
    mixedMoment B raw3585 raw3585Labels = mixedMoment B raw3585step0 raw3585step0Labels := by
      have hz : ∀ j, raw3585 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3585step0 = (fun i j => raw3585 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3585step0 raw3585; decide +kernel
      have hl : raw3585step0Labels = raw3585Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3585 raw3585Labels permutation346 hz
    mixedMoment B raw3585step0 raw3585step0Labels = mixedMoment B raw3585step1 raw3585step1Labels := by
      have ha : raw3585step1 = (fun i j => raw3585step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3585step1 raw3585step0; decide +kernel
      have hl : raw3585step1Labels = raw3585step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3585step0 raw3585step0Labels permutation151 permutation3
    mixedMoment B raw3585step1 raw3585step1Labels = mixedMoment B raw3585step2 raw3585step2Labels := by
      have ha : raw3585step2 = -raw3585step1 := by apply Matrix.ext; change ∀ i j, raw3585step2 i j = -(raw3585step1 i j); unfold raw3585step2 raw3585step1; decide +kernel
      have hl : raw3585step2Labels = raw3585step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2092 node2092Labels := by rfl

def raw3586 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw3586Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3586step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw3586step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3586step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![-3, 3, 0]]
def raw3586step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3586step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw3586step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3586 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3586 raw3586Labels = mixedMoment B node2092 node2092Labels := by
  calc
    mixedMoment B raw3586 raw3586Labels = mixedMoment B raw3586step0 raw3586step0Labels := by
      have hz : ∀ j, raw3586 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3586step0 = (fun i j => raw3586 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3586step0 raw3586; decide +kernel
      have hl : raw3586step0Labels = raw3586Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3586 raw3586Labels permutation265 hz
    mixedMoment B raw3586step0 raw3586step0Labels = mixedMoment B raw3586step1 raw3586step1Labels := by
      have ha : raw3586step1 = (fun i j => raw3586step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3586step1 raw3586step0; decide +kernel
      have hl : raw3586step1Labels = raw3586step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3586step0 raw3586step0Labels permutation151 permutation3
    mixedMoment B raw3586step1 raw3586step1Labels = mixedMoment B raw3586step2 raw3586step2Labels := by
      have ha : raw3586step2 = -raw3586step1 := by apply Matrix.ext; change ∀ i j, raw3586step2 i j = -(raw3586step1 i j); unfold raw3586step2 raw3586step1; decide +kernel
      have hl : raw3586step2Labels = raw3586step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2092 node2092Labels := by rfl

def raw3587 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![1, 1, -2], ![3, -3, 0]]
def raw3587Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3587step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 2, -1], ![1, 1, -2], ![3, -3, 0]]
def raw3587step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3587step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 1, -2], ![3, -3, 0]]
def raw3587step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3587step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, -1, 2], ![-3, 3, 0]]
def raw3587step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3587step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 1, -2], ![3, -3, 0]]
def raw3587step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3587 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3587 raw3587Labels = mixedMoment B node2113 node2113Labels := by
  calc
    mixedMoment B raw3587 raw3587Labels = mixedMoment B raw3587step0 raw3587step0Labels := by
      have hz : ∀ j, raw3587 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3587step0 = (fun i j => raw3587 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3587step0 raw3587; decide +kernel
      have hl : raw3587step0Labels = raw3587Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3587 raw3587Labels permutation346 hz
    mixedMoment B raw3587step0 raw3587step0Labels = mixedMoment B raw3587step1 raw3587step1Labels := by
      have hz : ∀ j, raw3587step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3587step1 = (fun i j => raw3587step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3587step1 raw3587step0; decide +kernel
      have hl : raw3587step1Labels = raw3587step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3587step0 raw3587step0Labels permutation56 hz
    mixedMoment B raw3587step1 raw3587step1Labels = mixedMoment B raw3587step2 raw3587step2Labels := by
      have ha : raw3587step2 = (fun i j => raw3587step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3587step2 raw3587step1; decide +kernel
      have hl : raw3587step2Labels = raw3587step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3587step1 raw3587step1Labels permutation31 permutation3
    mixedMoment B raw3587step2 raw3587step2Labels = mixedMoment B raw3587step3 raw3587step3Labels := by
      have ha : raw3587step3 = -raw3587step2 := by apply Matrix.ext; change ∀ i j, raw3587step3 i j = -(raw3587step2 i j); unfold raw3587step3 raw3587step2; decide +kernel
      have hl : raw3587step3Labels = raw3587step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2113 node2113Labels := by rfl

def raw3588 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw3588Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3588step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw3588step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3588step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw3588step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3588step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -3, 0], ![0, 2, -2], ![-1, 0, 1], ![-2, 1, 1]]
def raw3588step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3588step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw3588step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3588 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3588 raw3588Labels = mixedMoment B node3225 node3225Labels := by
  calc
    mixedMoment B raw3588 raw3588Labels = mixedMoment B raw3588step0 raw3588step0Labels := by
      have hz : ∀ j, raw3588 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3588step0 = (fun i j => raw3588 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3588step0 raw3588; decide +kernel
      have hl : raw3588step0Labels = raw3588Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3588 raw3588Labels permutation346 hz
    mixedMoment B raw3588step0 raw3588step0Labels = mixedMoment B raw3588step1 raw3588step1Labels := by
      have hz : ∀ j, raw3588step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3588step1 = (fun i j => raw3588step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3588step1 raw3588step0; decide +kernel
      have hl : raw3588step1Labels = raw3588step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3588step0 raw3588step0Labels permutation56 hz
    mixedMoment B raw3588step1 raw3588step1Labels = mixedMoment B raw3588step2 raw3588step2Labels := by
      have ha : raw3588step2 = (fun i j => raw3588step1 (permutation12 i) (permutation6 j)) := by apply Matrix.ext; unfold raw3588step2 raw3588step1; decide +kernel
      have hl : raw3588step2Labels = raw3588step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3588step1 raw3588step1Labels permutation12 permutation6
    mixedMoment B raw3588step2 raw3588step2Labels = mixedMoment B raw3588step3 raw3588step3Labels := by
      have ha : raw3588step3 = -raw3588step2 := by apply Matrix.ext; change ∀ i j, raw3588step3 i j = -(raw3588step2 i j); unfold raw3588step3 raw3588step2; decide +kernel
      have hl : raw3588step3Labels = raw3588step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3225 node3225Labels := by rfl

def raw3589 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2], ![4, -4, 0]]
def raw3589Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3589step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2], ![4, -4, 0]]
def raw3589step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3589step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 2, -2], ![4, -4, 0]]
def raw3589step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3589step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![0, -2, 2], ![-4, 3, 1]]
def raw3589step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3589step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 2, -2], ![4, -3, -1]]
def raw3589step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3589 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3589 raw3589Labels = mixedMoment B node797 node797Labels := by
  calc
    mixedMoment B raw3589 raw3589Labels = mixedMoment B raw3589step0 raw3589step0Labels := by
      have hz : ∀ j, raw3589 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3589step0 = (fun i j => raw3589 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3589step0 raw3589; decide +kernel
      have hl : raw3589step0Labels = raw3589Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3589 raw3589Labels permutation346 hz
    mixedMoment B raw3589step0 raw3589step0Labels = mixedMoment B raw3589step1 raw3589step1Labels := by
      have hz : ∀ j, raw3589step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3589step1 = (fun i j => raw3589step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3589step1 raw3589step0; decide +kernel
      have hl : raw3589step1Labels = raw3589step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3589step0 raw3589step0Labels permutation56 hz
    mixedMoment B raw3589step1 raw3589step1Labels = mixedMoment B raw3589step2 raw3589step2Labels := by
      have ha : raw3589step2 = (fun i j => raw3589step1 (permutation29 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3589step2 raw3589step1; decide +kernel
      have hl : raw3589step2Labels = raw3589step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3589step1 raw3589step1Labels permutation29 permutation3
    mixedMoment B raw3589step2 raw3589step2Labels = mixedMoment B raw3589step3 raw3589step3Labels := by
      have ha : raw3589step3 = -raw3589step2 := by apply Matrix.ext; change ∀ i j, raw3589step3 i j = -(raw3589step2 i j); unfold raw3589step3 raw3589step2; decide +kernel
      have hl : raw3589step3Labels = raw3589step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node797 node797Labels := by rfl

def raw3590 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2], ![4, -4, 0]]
def raw3590Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3590step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2], ![4, -4, 0]]
def raw3590step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3590step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-3, 3, 0]]
def raw3590step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3590step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw3590step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3590 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3590 raw3590Labels = mixedMoment B node795 node795Labels := by
  calc
    mixedMoment B raw3590 raw3590Labels = mixedMoment B raw3590step0 raw3590step0Labels := by
      have hz : ∀ j, raw3590 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3590step0 = (fun i j => raw3590 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3590step0 raw3590; decide +kernel
      have hl : raw3590step0Labels = raw3590Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3590 raw3590Labels permutation346 hz
    mixedMoment B raw3590step0 raw3590step0Labels = mixedMoment B raw3590step1 raw3590step1Labels := by
      have ha : raw3590step1 = (fun i j => raw3590step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3590step1 raw3590step0; decide +kernel
      have hl : raw3590step1Labels = raw3590step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3590step0 raw3590step0Labels permutation145 permutation3
    mixedMoment B raw3590step1 raw3590step1Labels = mixedMoment B raw3590step2 raw3590step2Labels := by
      have ha : raw3590step2 = -raw3590step1 := by apply Matrix.ext; change ∀ i j, raw3590step2 i j = -(raw3590step1 i j); unfold raw3590step2 raw3590step1; decide +kernel
      have hl : raw3590step2Labels = raw3590step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node795 node795Labels := by rfl

def raw3591 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2], ![4, -4, 0]]
def raw3591Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3591step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2], ![4, -4, 0]]
def raw3591step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3591step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-3, 3, 0]]
def raw3591step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3591step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw3591step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3591 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3591 raw3591Labels = mixedMoment B node795 node795Labels := by
  calc
    mixedMoment B raw3591 raw3591Labels = mixedMoment B raw3591step0 raw3591step0Labels := by
      have hz : ∀ j, raw3591 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3591step0 = (fun i j => raw3591 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3591step0 raw3591; decide +kernel
      have hl : raw3591step0Labels = raw3591Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3591 raw3591Labels permutation265 hz
    mixedMoment B raw3591step0 raw3591step0Labels = mixedMoment B raw3591step1 raw3591step1Labels := by
      have ha : raw3591step1 = (fun i j => raw3591step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3591step1 raw3591step0; decide +kernel
      have hl : raw3591step1Labels = raw3591step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3591step0 raw3591step0Labels permutation145 permutation3
    mixedMoment B raw3591step1 raw3591step1Labels = mixedMoment B raw3591step2 raw3591step2Labels := by
      have ha : raw3591step2 = -raw3591step1 := by apply Matrix.ext; change ∀ i j, raw3591step2 i j = -(raw3591step1 i j); unfold raw3591step2 raw3591step1; decide +kernel
      have hl : raw3591step2Labels = raw3591step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node795 node795Labels := by rfl

def raw3592 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![0, 2, -2], ![4, -4, 0]]
def raw3592Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3592step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 2, -1], ![0, 2, -2], ![4, -4, 0]]
def raw3592step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3592step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 2, -2], ![4, -4, 0]]
def raw3592step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3592step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -2, 2], ![-1, -1, 2], ![-3, 3, 0]]
def raw3592step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3592step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, 1, -2], ![3, -3, 0]]
def raw3592step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3592 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3592 raw3592Labels = mixedMoment B node829 node829Labels := by
  calc
    mixedMoment B raw3592 raw3592Labels = mixedMoment B raw3592step0 raw3592step0Labels := by
      have hz : ∀ j, raw3592 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3592step0 = (fun i j => raw3592 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3592step0 raw3592; decide +kernel
      have hl : raw3592step0Labels = raw3592Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3592 raw3592Labels permutation346 hz
    mixedMoment B raw3592step0 raw3592step0Labels = mixedMoment B raw3592step1 raw3592step1Labels := by
      have hz : ∀ j, raw3592step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3592step1 = (fun i j => raw3592step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3592step1 raw3592step0; decide +kernel
      have hl : raw3592step1Labels = raw3592step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3592step0 raw3592step0Labels permutation56 hz
    mixedMoment B raw3592step1 raw3592step1Labels = mixedMoment B raw3592step2 raw3592step2Labels := by
      have ha : raw3592step2 = (fun i j => raw3592step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3592step2 raw3592step1; decide +kernel
      have hl : raw3592step2Labels = raw3592step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3592step1 raw3592step1Labels permutation31 permutation3
    mixedMoment B raw3592step2 raw3592step2Labels = mixedMoment B raw3592step3 raw3592step3Labels := by
      have ha : raw3592step3 = -raw3592step2 := by apply Matrix.ext; change ∀ i j, raw3592step3 i j = -(raw3592step2 i j); unfold raw3592step3 raw3592step2; decide +kernel
      have hl : raw3592step3Labels = raw3592step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node829 node829Labels := by rfl

def raw3593 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![-1, 3, -2], ![4, -4, 0]]
def raw3593Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3593step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![-1, 3, -2], ![4, -4, 0]]
def raw3593step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3593step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 3, -2], ![4, -4, 0]]
def raw3593step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3593step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, -2, 3], ![-3, 3, 0]]
def raw3593step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3593step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 2, -3], ![3, -3, 0]]
def raw3593step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3593 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3593 raw3593Labels = mixedMoment B node814 node814Labels := by
  calc
    mixedMoment B raw3593 raw3593Labels = mixedMoment B raw3593step0 raw3593step0Labels := by
      have hz : ∀ j, raw3593 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3593step0 = (fun i j => raw3593 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3593step0 raw3593; decide +kernel
      have hl : raw3593step0Labels = raw3593Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3593 raw3593Labels permutation346 hz
    mixedMoment B raw3593step0 raw3593step0Labels = mixedMoment B raw3593step1 raw3593step1Labels := by
      have hz : ∀ j, raw3593step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3593step1 = (fun i j => raw3593step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3593step1 raw3593step0; decide +kernel
      have hl : raw3593step1Labels = raw3593step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3593step0 raw3593step0Labels permutation56 hz
    mixedMoment B raw3593step1 raw3593step1Labels = mixedMoment B raw3593step2 raw3593step2Labels := by
      have ha : raw3593step2 = (fun i j => raw3593step1 (permutation29 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3593step2 raw3593step1; decide +kernel
      have hl : raw3593step2Labels = raw3593step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3593step1 raw3593step1Labels permutation29 permutation3
    mixedMoment B raw3593step2 raw3593step2Labels = mixedMoment B raw3593step3 raw3593step3Labels := by
      have ha : raw3593step3 = -raw3593step2 := by apply Matrix.ext; change ∀ i j, raw3593step3 i j = -(raw3593step2 i j); unfold raw3593step3 raw3593step2; decide +kernel
      have hl : raw3593step3Labels = raw3593step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node814 node814Labels := by rfl

def raw3594 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3594Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3594step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3594step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3594step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw3594step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3594step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw3594step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3594 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3594 raw3594Labels = mixedMoment B node2133 node2133Labels := by
  calc
    mixedMoment B raw3594 raw3594Labels = mixedMoment B raw3594step0 raw3594step0Labels := by
      have hz : ∀ j, raw3594 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3594step0 = (fun i j => raw3594 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3594step0 raw3594; decide +kernel
      have hl : raw3594step0Labels = raw3594Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3594 raw3594Labels permutation346 hz
    mixedMoment B raw3594step0 raw3594step0Labels = mixedMoment B raw3594step1 raw3594step1Labels := by
      have ha : raw3594step1 = (fun i j => raw3594step0 (permutation130 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3594step1 raw3594step0; decide +kernel
      have hl : raw3594step1Labels = raw3594step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3594step0 raw3594step0Labels permutation130 permutation5
    mixedMoment B raw3594step1 raw3594step1Labels = mixedMoment B raw3594step2 raw3594step2Labels := by
      have ha : raw3594step2 = raw3594step1 := by apply Matrix.ext; unfold raw3594step2 raw3594step1; decide +kernel
      have hl : raw3594step1Labels = labelEmbedding1 ∘ raw3594step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3594step1 raw3594step1Labels raw3594step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2133 node2133Labels := by rfl

def raw3595 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3595Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3595step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3595step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3595step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw3595step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3595step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw3595step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3595 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3595 raw3595Labels = mixedMoment B node2133 node2133Labels := by
  calc
    mixedMoment B raw3595 raw3595Labels = mixedMoment B raw3595step0 raw3595step0Labels := by
      have hz : ∀ j, raw3595 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3595step0 = (fun i j => raw3595 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3595step0 raw3595; decide +kernel
      have hl : raw3595step0Labels = raw3595Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3595 raw3595Labels permutation265 hz
    mixedMoment B raw3595step0 raw3595step0Labels = mixedMoment B raw3595step1 raw3595step1Labels := by
      have ha : raw3595step1 = (fun i j => raw3595step0 (permutation130 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3595step1 raw3595step0; decide +kernel
      have hl : raw3595step1Labels = raw3595step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3595step0 raw3595step0Labels permutation130 permutation5
    mixedMoment B raw3595step1 raw3595step1Labels = mixedMoment B raw3595step2 raw3595step2Labels := by
      have ha : raw3595step2 = raw3595step1 := by apply Matrix.ext; unfold raw3595step2 raw3595step1; decide +kernel
      have hl : raw3595step1Labels = labelEmbedding1 ∘ raw3595step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3595step1 raw3595step1Labels raw3595step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2133 node2133Labels := by rfl

def raw3596 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3596Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3596step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![-1, 2, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3596step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3596step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3596step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3596step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![2, -2, 0], ![2, -1, -1]]
def raw3596step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3596step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![2, -2, 0], ![2, -1, -1]]
def raw3596step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3596 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3596 raw3596Labels = mixedMoment B node2138 node2138Labels := by
  calc
    mixedMoment B raw3596 raw3596Labels = mixedMoment B raw3596step0 raw3596step0Labels := by
      have hz : ∀ j, raw3596 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3596step0 = (fun i j => raw3596 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3596step0 raw3596; decide +kernel
      have hl : raw3596step0Labels = raw3596Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3596 raw3596Labels permutation346 hz
    mixedMoment B raw3596step0 raw3596step0Labels = mixedMoment B raw3596step1 raw3596step1Labels := by
      have hz : ∀ j, raw3596step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3596step1 = (fun i j => raw3596step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3596step1 raw3596step0; decide +kernel
      have hl : raw3596step1Labels = raw3596step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3596step0 raw3596step0Labels permutation56 hz
    mixedMoment B raw3596step1 raw3596step1Labels = mixedMoment B raw3596step2 raw3596step2Labels := by
      have ha : raw3596step2 = (fun i j => raw3596step1 (permutation27 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3596step2 raw3596step1; decide +kernel
      have hl : raw3596step2Labels = raw3596step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3596step1 raw3596step1Labels permutation27 permutation5
    mixedMoment B raw3596step2 raw3596step2Labels = mixedMoment B raw3596step3 raw3596step3Labels := by
      have ha : raw3596step3 = raw3596step2 := by apply Matrix.ext; unfold raw3596step3 raw3596step2; decide +kernel
      have hl : raw3596step2Labels = labelEmbedding1 ∘ raw3596step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3596step2 raw3596step2Labels raw3596step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2138 node2138Labels := by rfl

def raw3597 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![-1, 3, -2], ![3, -3, 0]]
def raw3597Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3597step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 1, -1], ![-1, 3, -2], ![3, -3, 0]]
def raw3597step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3597step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![-1, 3, -2], ![3, -3, 0]]
def raw3597step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3597step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![3, -2, -1]]
def raw3597step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3597step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![3, -2, -1]]
def raw3597step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3597 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3597 raw3597Labels = mixedMoment B node2134 node2134Labels := by
  calc
    mixedMoment B raw3597 raw3597Labels = mixedMoment B raw3597step0 raw3597step0Labels := by
      have hz : ∀ j, raw3597 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3597step0 = (fun i j => raw3597 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3597step0 raw3597; decide +kernel
      have hl : raw3597step0Labels = raw3597Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3597 raw3597Labels permutation346 hz
    mixedMoment B raw3597step0 raw3597step0Labels = mixedMoment B raw3597step1 raw3597step1Labels := by
      have hz : ∀ j, raw3597step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3597step1 = (fun i j => raw3597step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3597step1 raw3597step0; decide +kernel
      have hl : raw3597step1Labels = raw3597step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3597step0 raw3597step0Labels permutation56 hz
    mixedMoment B raw3597step1 raw3597step1Labels = mixedMoment B raw3597step2 raw3597step2Labels := by
      have ha : raw3597step2 = (fun i j => raw3597step1 (permutation26 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3597step2 raw3597step1; decide +kernel
      have hl : raw3597step2Labels = raw3597step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3597step1 raw3597step1Labels permutation26 permutation5
    mixedMoment B raw3597step2 raw3597step2Labels = mixedMoment B raw3597step3 raw3597step3Labels := by
      have ha : raw3597step3 = raw3597step2 := by apply Matrix.ext; unfold raw3597step3 raw3597step2; decide +kernel
      have hl : raw3597step2Labels = labelEmbedding1 ∘ raw3597step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3597step2 raw3597step2Labels raw3597step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2134 node2134Labels := by rfl

def raw3598 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw3598Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3598step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw3598step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3598step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw3598step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3598step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw3598step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3598step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw3598step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3598step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw3598step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3598 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3598 raw3598Labels = mixedMoment B node2776 node2776Labels := by
  calc
    mixedMoment B raw3598 raw3598Labels = mixedMoment B raw3598step0 raw3598step0Labels := by
      have hz : ∀ j, raw3598 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3598step0 = (fun i j => raw3598 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3598step0 raw3598; decide +kernel
      have hl : raw3598step0Labels = raw3598Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3598 raw3598Labels permutation346 hz
    mixedMoment B raw3598step0 raw3598step0Labels = mixedMoment B raw3598step1 raw3598step1Labels := by
      have hz : ∀ j, raw3598step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3598step1 = (fun i j => raw3598step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3598step1 raw3598step0; decide +kernel
      have hl : raw3598step1Labels = raw3598step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3598step0 raw3598step0Labels permutation56 hz
    mixedMoment B raw3598step1 raw3598step1Labels = mixedMoment B raw3598step2 raw3598step2Labels := by
      have ha : raw3598step2 = (fun i j => raw3598step1 (permutation12 i) (permutation7 j)) := by apply Matrix.ext; unfold raw3598step2 raw3598step1; decide +kernel
      have hl : raw3598step2Labels = raw3598step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3598step1 raw3598step1Labels permutation12 permutation7
    mixedMoment B raw3598step2 raw3598step2Labels = mixedMoment B raw3598step3 raw3598step3Labels := by
      have ha : raw3598step3 = -raw3598step2 := by apply Matrix.ext; change ∀ i j, raw3598step3 i j = -(raw3598step2 i j); unfold raw3598step3 raw3598step2; decide +kernel
      have hl : raw3598step3Labels = raw3598step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3598step3 raw3598step3Labels = mixedMoment B raw3598step4 raw3598step4Labels := by
      have ha : raw3598step4 = raw3598step3 := by apply Matrix.ext; unfold raw3598step4 raw3598step3; decide +kernel
      have hl : raw3598step3Labels = labelEmbedding1 ∘ raw3598step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3598step3 raw3598step3Labels raw3598step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2776 node2776Labels := by rfl

def raw3599 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3599Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3599step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3599step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3599step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -3, 3], ![-1, 1, 0], ![-2, 2, 0]]
def raw3599step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3599step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 3, -3], ![1, -1, 0], ![2, -2, 0]]
def raw3599step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3599step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 3, -3], ![1, -1, 0], ![2, -2, 0]]
def raw3599step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3599 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3599 raw3599Labels = mixedMoment B node1718 node1718Labels := by
  calc
    mixedMoment B raw3599 raw3599Labels = mixedMoment B raw3599step0 raw3599step0Labels := by
      have hz : ∀ j, raw3599 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3599step0 = (fun i j => raw3599 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3599step0 raw3599; decide +kernel
      have hl : raw3599step0Labels = raw3599Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3599 raw3599Labels permutation346 hz
    mixedMoment B raw3599step0 raw3599step0Labels = mixedMoment B raw3599step1 raw3599step1Labels := by
      have ha : raw3599step1 = (fun i j => raw3599step0 (permutation36 i) (permutation7 j)) := by apply Matrix.ext; unfold raw3599step1 raw3599step0; decide +kernel
      have hl : raw3599step1Labels = raw3599step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3599step0 raw3599step0Labels permutation36 permutation7
    mixedMoment B raw3599step1 raw3599step1Labels = mixedMoment B raw3599step2 raw3599step2Labels := by
      have ha : raw3599step2 = -raw3599step1 := by apply Matrix.ext; change ∀ i j, raw3599step2 i j = -(raw3599step1 i j); unfold raw3599step2 raw3599step1; decide +kernel
      have hl : raw3599step2Labels = raw3599step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3599step2 raw3599step2Labels = mixedMoment B raw3599step3 raw3599step3Labels := by
      have ha : raw3599step3 = raw3599step2 := by apply Matrix.ext; unfold raw3599step3 raw3599step2; decide +kernel
      have hl : raw3599step2Labels = labelEmbedding1 ∘ raw3599step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3599step2 raw3599step2Labels raw3599step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1718 node1718Labels := by rfl

def raw3600 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3600Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3600step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw3600step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3600step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw3600step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3600 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3600 raw3600Labels = mixedMoment B node1931 node1931Labels := by
  calc
    mixedMoment B raw3600 raw3600Labels = mixedMoment B raw3600step0 raw3600step0Labels := by
      have ha : raw3600step0 = (fun i j => raw3600 (permutation604 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3600step0 raw3600; decide +kernel
      have hl : raw3600step0Labels = raw3600Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3600 raw3600Labels permutation604 permutation5
    mixedMoment B raw3600step0 raw3600step0Labels = mixedMoment B raw3600step1 raw3600step1Labels := by
      have ha : raw3600step1 = raw3600step0 := by apply Matrix.ext; unfold raw3600step1 raw3600step0; decide +kernel
      have hl : raw3600step0Labels = labelEmbedding1 ∘ raw3600step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3600step0 raw3600step0Labels raw3600step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1931 node1931Labels := by rfl

def raw3601 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![0, 0, 0], ![-1, 2, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3601Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3601step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![-1, 2, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3601step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3601step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 3, -3], ![2, -2, 0], ![2, -1, -1]]
def raw3601step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3601step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 3, -3], ![2, -2, 0], ![2, -1, -1]]
def raw3601step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3601 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3601 raw3601Labels = mixedMoment B node1934 node1934Labels := by
  calc
    mixedMoment B raw3601 raw3601Labels = mixedMoment B raw3601step0 raw3601step0Labels := by
      have hz : ∀ j, raw3601 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3601step0 = (fun i j => raw3601 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3601step0 raw3601; decide +kernel
      have hl : raw3601step0Labels = raw3601Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3601 raw3601Labels permutation346 hz
    mixedMoment B raw3601step0 raw3601step0Labels = mixedMoment B raw3601step1 raw3601step1Labels := by
      have ha : raw3601step1 = (fun i j => raw3601step0 (permutation135 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3601step1 raw3601step0; decide +kernel
      have hl : raw3601step1Labels = raw3601step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3601step0 raw3601step0Labels permutation135 permutation5
    mixedMoment B raw3601step1 raw3601step1Labels = mixedMoment B raw3601step2 raw3601step2Labels := by
      have ha : raw3601step2 = raw3601step1 := by apply Matrix.ext; unfold raw3601step2 raw3601step1; decide +kernel
      have hl : raw3601step1Labels = labelEmbedding1 ∘ raw3601step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3601step1 raw3601step1Labels raw3601step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1934 node1934Labels := by rfl

def raw3602 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![-1, 3, -2], ![3, -3, 0]]
def raw3602Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3602step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![0, 1, -1], ![-1, 3, -2], ![3, -3, 0]]
def raw3602step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3602step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 3, -3], ![1, -1, 0], ![3, -2, -1]]
def raw3602step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3602step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 3, -3], ![1, -1, 0], ![3, -2, -1]]
def raw3602step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3602 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3602 raw3602Labels = mixedMoment B node1932 node1932Labels := by
  calc
    mixedMoment B raw3602 raw3602Labels = mixedMoment B raw3602step0 raw3602step0Labels := by
      have hz : ∀ j, raw3602 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3602step0 = (fun i j => raw3602 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3602step0 raw3602; decide +kernel
      have hl : raw3602step0Labels = raw3602Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3602 raw3602Labels permutation346 hz
    mixedMoment B raw3602step0 raw3602step0Labels = mixedMoment B raw3602step1 raw3602step1Labels := by
      have ha : raw3602step1 = (fun i j => raw3602step0 (permutation134 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3602step1 raw3602step0; decide +kernel
      have hl : raw3602step1Labels = raw3602step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3602step0 raw3602step0Labels permutation134 permutation5
    mixedMoment B raw3602step1 raw3602step1Labels = mixedMoment B raw3602step2 raw3602step2Labels := by
      have ha : raw3602step2 = raw3602step1 := by apply Matrix.ext; unfold raw3602step2 raw3602step1; decide +kernel
      have hl : raw3602step1Labels = labelEmbedding1 ∘ raw3602step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3602step1 raw3602step1Labels raw3602step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1932 node1932Labels := by rfl

def raw3603 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw3603Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3603step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw3603step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3603step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw3603step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3603step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw3603step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3603step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw3603step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3603 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3603 raw3603Labels = mixedMoment B node2253 node2253Labels := by
  calc
    mixedMoment B raw3603 raw3603Labels = mixedMoment B raw3603step0 raw3603step0Labels := by
      have hz : ∀ j, raw3603 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3603step0 = (fun i j => raw3603 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3603step0 raw3603; decide +kernel
      have hl : raw3603step0Labels = raw3603Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3603 raw3603Labels permutation346 hz
    mixedMoment B raw3603step0 raw3603step0Labels = mixedMoment B raw3603step1 raw3603step1Labels := by
      have ha : raw3603step1 = (fun i j => raw3603step0 (permutation36 i) (permutation7 j)) := by apply Matrix.ext; unfold raw3603step1 raw3603step0; decide +kernel
      have hl : raw3603step1Labels = raw3603step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3603step0 raw3603step0Labels permutation36 permutation7
    mixedMoment B raw3603step1 raw3603step1Labels = mixedMoment B raw3603step2 raw3603step2Labels := by
      have ha : raw3603step2 = -raw3603step1 := by apply Matrix.ext; change ∀ i j, raw3603step2 i j = -(raw3603step1 i j); unfold raw3603step2 raw3603step1; decide +kernel
      have hl : raw3603step2Labels = raw3603step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3603step2 raw3603step2Labels = mixedMoment B raw3603step3 raw3603step3Labels := by
      have ha : raw3603step3 = raw3603step2 := by apply Matrix.ext; unfold raw3603step3 raw3603step2; decide +kernel
      have hl : raw3603step2Labels = labelEmbedding1 ∘ raw3603step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3603step2 raw3603step2Labels raw3603step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2253 node2253Labels := by rfl

def raw3604 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3604Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3604step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3604step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3604step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -3, 3], ![-1, 1, 0], ![-2, 2, 0]]
def raw3604step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3604step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 3, -3], ![1, -1, 0], ![2, -2, 0]]
def raw3604step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3604step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 3, -3], ![1, -1, 0], ![2, -2, 0]]
def raw3604step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3604 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3604 raw3604Labels = mixedMoment B node1718 node1718Labels := by
  calc
    mixedMoment B raw3604 raw3604Labels = mixedMoment B raw3604step0 raw3604step0Labels := by
      have hz : ∀ j, raw3604 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3604step0 = (fun i j => raw3604 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3604step0 raw3604; decide +kernel
      have hl : raw3604step0Labels = raw3604Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3604 raw3604Labels permutation265 hz
    mixedMoment B raw3604step0 raw3604step0Labels = mixedMoment B raw3604step1 raw3604step1Labels := by
      have ha : raw3604step1 = (fun i j => raw3604step0 (permutation36 i) (permutation7 j)) := by apply Matrix.ext; unfold raw3604step1 raw3604step0; decide +kernel
      have hl : raw3604step1Labels = raw3604step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3604step0 raw3604step0Labels permutation36 permutation7
    mixedMoment B raw3604step1 raw3604step1Labels = mixedMoment B raw3604step2 raw3604step2Labels := by
      have ha : raw3604step2 = -raw3604step1 := by apply Matrix.ext; change ∀ i j, raw3604step2 i j = -(raw3604step1 i j); unfold raw3604step2 raw3604step1; decide +kernel
      have hl : raw3604step2Labels = raw3604step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3604step2 raw3604step2Labels = mixedMoment B raw3604step3 raw3604step3Labels := by
      have ha : raw3604step3 = raw3604step2 := by apply Matrix.ext; unfold raw3604step3 raw3604step2; decide +kernel
      have hl : raw3604step2Labels = labelEmbedding1 ∘ raw3604step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3604step2 raw3604step2Labels raw3604step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1718 node1718Labels := by rfl

def raw3605 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3605Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3605step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw3605step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3605step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw3605step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3605 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3605 raw3605Labels = mixedMoment B node1931 node1931Labels := by
  calc
    mixedMoment B raw3605 raw3605Labels = mixedMoment B raw3605step0 raw3605step0Labels := by
      have ha : raw3605step0 = (fun i j => raw3605 (permutation625 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3605step0 raw3605; decide +kernel
      have hl : raw3605step0Labels = raw3605Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3605 raw3605Labels permutation625 permutation5
    mixedMoment B raw3605step0 raw3605step0Labels = mixedMoment B raw3605step1 raw3605step1Labels := by
      have ha : raw3605step1 = raw3605step0 := by apply Matrix.ext; unfold raw3605step1 raw3605step0; decide +kernel
      have hl : raw3605step0Labels = labelEmbedding1 ∘ raw3605step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3605step0 raw3605step0Labels raw3605step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1931 node1931Labels := by rfl

def raw3606 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, -1, 0], ![-1, 2, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3606Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3606step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![-1, 2, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3606step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3606step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 3, -3], ![2, -2, 0], ![2, -1, -1]]
def raw3606step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3606step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 3, -3], ![2, -2, 0], ![2, -1, -1]]
def raw3606step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3606 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3606 raw3606Labels = mixedMoment B node1934 node1934Labels := by
  calc
    mixedMoment B raw3606 raw3606Labels = mixedMoment B raw3606step0 raw3606step0Labels := by
      have hz : ∀ j, raw3606 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3606step0 = (fun i j => raw3606 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3606step0 raw3606; decide +kernel
      have hl : raw3606step0Labels = raw3606Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3606 raw3606Labels permutation265 hz
    mixedMoment B raw3606step0 raw3606step0Labels = mixedMoment B raw3606step1 raw3606step1Labels := by
      have ha : raw3606step1 = (fun i j => raw3606step0 (permutation135 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3606step1 raw3606step0; decide +kernel
      have hl : raw3606step1Labels = raw3606step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3606step0 raw3606step0Labels permutation135 permutation5
    mixedMoment B raw3606step1 raw3606step1Labels = mixedMoment B raw3606step2 raw3606step2Labels := by
      have ha : raw3606step2 = raw3606step1 := by apply Matrix.ext; unfold raw3606step2 raw3606step1; decide +kernel
      have hl : raw3606step1Labels = labelEmbedding1 ∘ raw3606step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3606step1 raw3606step1Labels raw3606step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1934 node1934Labels := by rfl

def raw3607 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![-1, 3, -2], ![3, -3, 0]]
def raw3607Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3607step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![0, 1, -1], ![-1, 3, -2], ![3, -3, 0]]
def raw3607step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3607step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 3, -3], ![1, -1, 0], ![3, -2, -1]]
def raw3607step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3607step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 3, -3], ![1, -1, 0], ![3, -2, -1]]
def raw3607step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3607 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3607 raw3607Labels = mixedMoment B node1932 node1932Labels := by
  calc
    mixedMoment B raw3607 raw3607Labels = mixedMoment B raw3607step0 raw3607step0Labels := by
      have hz : ∀ j, raw3607 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3607step0 = (fun i j => raw3607 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3607step0 raw3607; decide +kernel
      have hl : raw3607step0Labels = raw3607Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3607 raw3607Labels permutation265 hz
    mixedMoment B raw3607step0 raw3607step0Labels = mixedMoment B raw3607step1 raw3607step1Labels := by
      have ha : raw3607step1 = (fun i j => raw3607step0 (permutation134 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3607step1 raw3607step0; decide +kernel
      have hl : raw3607step1Labels = raw3607step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3607step0 raw3607step0Labels permutation134 permutation5
    mixedMoment B raw3607step1 raw3607step1Labels = mixedMoment B raw3607step2 raw3607step2Labels := by
      have ha : raw3607step2 = raw3607step1 := by apply Matrix.ext; unfold raw3607step2 raw3607step1; decide +kernel
      have hl : raw3607step1Labels = labelEmbedding1 ∘ raw3607step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3607step1 raw3607step1Labels raw3607step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1932 node1932Labels := by rfl

def raw3608 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw3608Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3608step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw3608step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3608step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw3608step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3608step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw3608step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3608step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw3608step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3608 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3608 raw3608Labels = mixedMoment B node2253 node2253Labels := by
  calc
    mixedMoment B raw3608 raw3608Labels = mixedMoment B raw3608step0 raw3608step0Labels := by
      have hz : ∀ j, raw3608 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3608step0 = (fun i j => raw3608 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3608step0 raw3608; decide +kernel
      have hl : raw3608step0Labels = raw3608Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3608 raw3608Labels permutation265 hz
    mixedMoment B raw3608step0 raw3608step0Labels = mixedMoment B raw3608step1 raw3608step1Labels := by
      have ha : raw3608step1 = (fun i j => raw3608step0 (permutation36 i) (permutation7 j)) := by apply Matrix.ext; unfold raw3608step1 raw3608step0; decide +kernel
      have hl : raw3608step1Labels = raw3608step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3608step0 raw3608step0Labels permutation36 permutation7
    mixedMoment B raw3608step1 raw3608step1Labels = mixedMoment B raw3608step2 raw3608step2Labels := by
      have ha : raw3608step2 = -raw3608step1 := by apply Matrix.ext; change ∀ i j, raw3608step2 i j = -(raw3608step1 i j); unfold raw3608step2 raw3608step1; decide +kernel
      have hl : raw3608step2Labels = raw3608step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3608step2 raw3608step2Labels = mixedMoment B raw3608step3 raw3608step3Labels := by
      have ha : raw3608step3 = raw3608step2 := by apply Matrix.ext; unfold raw3608step3 raw3608step2; decide +kernel
      have hl : raw3608step2Labels = labelEmbedding1 ∘ raw3608step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3608step2 raw3608step2Labels raw3608step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2253 node2253Labels := by rfl

def raw3609 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3609Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3609step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 0, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3609step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3609step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3609step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3609step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -3, 3], ![-1, 0, 1], ![-2, 2, 0]]
def raw3609step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3609step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, 0, -1], ![2, -2, 0]]
def raw3609step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3609step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, 0, -1], ![2, -2, 0]]
def raw3609step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3609 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3609 raw3609Labels = mixedMoment B node1746 node1746Labels := by
  calc
    mixedMoment B raw3609 raw3609Labels = mixedMoment B raw3609step0 raw3609step0Labels := by
      have hz : ∀ j, raw3609 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3609step0 = (fun i j => raw3609 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3609step0 raw3609; decide +kernel
      have hl : raw3609step0Labels = raw3609Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3609 raw3609Labels permutation346 hz
    mixedMoment B raw3609step0 raw3609step0Labels = mixedMoment B raw3609step1 raw3609step1Labels := by
      have hz : ∀ j, raw3609step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3609step1 = (fun i j => raw3609step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3609step1 raw3609step0; decide +kernel
      have hl : raw3609step1Labels = raw3609step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3609step0 raw3609step0Labels permutation56 hz
    mixedMoment B raw3609step1 raw3609step1Labels = mixedMoment B raw3609step2 raw3609step2Labels := by
      have ha : raw3609step2 = (fun i j => raw3609step1 (permutation12 i) (permutation7 j)) := by apply Matrix.ext; unfold raw3609step2 raw3609step1; decide +kernel
      have hl : raw3609step2Labels = raw3609step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3609step1 raw3609step1Labels permutation12 permutation7
    mixedMoment B raw3609step2 raw3609step2Labels = mixedMoment B raw3609step3 raw3609step3Labels := by
      have ha : raw3609step3 = -raw3609step2 := by apply Matrix.ext; change ∀ i j, raw3609step3 i j = -(raw3609step2 i j); unfold raw3609step3 raw3609step2; decide +kernel
      have hl : raw3609step3Labels = raw3609step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3609step3 raw3609step3Labels = mixedMoment B raw3609step4 raw3609step4Labels := by
      have ha : raw3609step4 = raw3609step3 := by apply Matrix.ext; unfold raw3609step4 raw3609step3; decide +kernel
      have hl : raw3609step3Labels = labelEmbedding1 ∘ raw3609step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3609step3 raw3609step3Labels raw3609step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1746 node1746Labels := by rfl

def raw3610 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3610Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3610step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3610step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3610step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1], ![2, -2, 0]]
def raw3610step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3610step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1], ![2, -2, 0]]
def raw3610step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3610 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3610 raw3610Labels = mixedMoment B node2221 node2221Labels := by
  calc
    mixedMoment B raw3610 raw3610Labels = mixedMoment B raw3610step0 raw3610step0Labels := by
      have hz : ∀ j, raw3610 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3610step0 = (fun i j => raw3610 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3610step0 raw3610; decide +kernel
      have hl : raw3610step0Labels = raw3610Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3610 raw3610Labels permutation346 hz
    mixedMoment B raw3610step0 raw3610step0Labels = mixedMoment B raw3610step1 raw3610step1Labels := by
      have ha : raw3610step1 = (fun i j => raw3610step0 (permutation140 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3610step1 raw3610step0; decide +kernel
      have hl : raw3610step1Labels = raw3610step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3610step0 raw3610step0Labels permutation140 permutation5
    mixedMoment B raw3610step1 raw3610step1Labels = mixedMoment B raw3610step2 raw3610step2Labels := by
      have ha : raw3610step2 = raw3610step1 := by apply Matrix.ext; unfold raw3610step2 raw3610step1; decide +kernel
      have hl : raw3610step1Labels = labelEmbedding1 ∘ raw3610step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3610step1 raw3610step1Labels raw3610step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2221 node2221Labels := by rfl

def raw3611 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3611Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3611step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3611step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3611step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1], ![2, -2, 0]]
def raw3611step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3611step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1], ![2, -2, 0]]
def raw3611step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3611 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3611 raw3611Labels = mixedMoment B node2221 node2221Labels := by
  calc
    mixedMoment B raw3611 raw3611Labels = mixedMoment B raw3611step0 raw3611step0Labels := by
      have hz : ∀ j, raw3611 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3611step0 = (fun i j => raw3611 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3611step0 raw3611; decide +kernel
      have hl : raw3611step0Labels = raw3611Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3611 raw3611Labels permutation265 hz
    mixedMoment B raw3611step0 raw3611step0Labels = mixedMoment B raw3611step1 raw3611step1Labels := by
      have ha : raw3611step1 = (fun i j => raw3611step0 (permutation140 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3611step1 raw3611step0; decide +kernel
      have hl : raw3611step1Labels = raw3611step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3611step0 raw3611step0Labels permutation140 permutation5
    mixedMoment B raw3611step1 raw3611step1Labels = mixedMoment B raw3611step2 raw3611step2Labels := by
      have ha : raw3611step2 = raw3611step1 := by apply Matrix.ext; unfold raw3611step2 raw3611step1; decide +kernel
      have hl : raw3611step1Labels = labelEmbedding1 ∘ raw3611step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3611step1 raw3611step1Labels raw3611step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2221 node2221Labels := by rfl

def raw3612 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![-1, 3, -2], ![3, -3, 0]]
def raw3612Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3612step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 0, -1], ![-1, 3, -2], ![3, -3, 0]]
def raw3612step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3612step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![-1, 3, -2], ![3, -3, 0]]
def raw3612step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3612step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![3, -2, -1]]
def raw3612step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3612step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![3, -2, -1]]
def raw3612step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3612 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3612 raw3612Labels = mixedMoment B node2222 node2222Labels := by
  calc
    mixedMoment B raw3612 raw3612Labels = mixedMoment B raw3612step0 raw3612step0Labels := by
      have hz : ∀ j, raw3612 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3612step0 = (fun i j => raw3612 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3612step0 raw3612; decide +kernel
      have hl : raw3612step0Labels = raw3612Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3612 raw3612Labels permutation346 hz
    mixedMoment B raw3612step0 raw3612step0Labels = mixedMoment B raw3612step1 raw3612step1Labels := by
      have hz : ∀ j, raw3612step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3612step1 = (fun i j => raw3612step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3612step1 raw3612step0; decide +kernel
      have hl : raw3612step1Labels = raw3612step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3612step0 raw3612step0Labels permutation56 hz
    mixedMoment B raw3612step1 raw3612step1Labels = mixedMoment B raw3612step2 raw3612step2Labels := by
      have ha : raw3612step2 = (fun i j => raw3612step1 (permutation28 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3612step2 raw3612step1; decide +kernel
      have hl : raw3612step2Labels = raw3612step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3612step1 raw3612step1Labels permutation28 permutation5
    mixedMoment B raw3612step2 raw3612step2Labels = mixedMoment B raw3612step3 raw3612step3Labels := by
      have ha : raw3612step3 = raw3612step2 := by apply Matrix.ext; unfold raw3612step3 raw3612step2; decide +kernel
      have hl : raw3612step2Labels = labelEmbedding1 ∘ raw3612step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3612step2 raw3612step2Labels raw3612step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2222 node2222Labels := by rfl

def raw3613 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![0, 2, -2], ![2, -2, 0]]
def raw3613Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3613step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 0, -1], ![0, 2, -2], ![2, -2, 0]]
def raw3613step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3613step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 2, -2], ![2, -2, 0]]
def raw3613step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3613step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw3613step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3613step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw3613step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3613step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw3613step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3613 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3613 raw3613Labels = mixedMoment B node2279 node2279Labels := by
  calc
    mixedMoment B raw3613 raw3613Labels = mixedMoment B raw3613step0 raw3613step0Labels := by
      have hz : ∀ j, raw3613 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3613step0 = (fun i j => raw3613 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3613step0 raw3613; decide +kernel
      have hl : raw3613step0Labels = raw3613Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3613 raw3613Labels permutation346 hz
    mixedMoment B raw3613step0 raw3613step0Labels = mixedMoment B raw3613step1 raw3613step1Labels := by
      have hz : ∀ j, raw3613step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3613step1 = (fun i j => raw3613step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3613step1 raw3613step0; decide +kernel
      have hl : raw3613step1Labels = raw3613step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3613step0 raw3613step0Labels permutation56 hz
    mixedMoment B raw3613step1 raw3613step1Labels = mixedMoment B raw3613step2 raw3613step2Labels := by
      have ha : raw3613step2 = (fun i j => raw3613step1 (permutation12 i) (permutation7 j)) := by apply Matrix.ext; unfold raw3613step2 raw3613step1; decide +kernel
      have hl : raw3613step2Labels = raw3613step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3613step1 raw3613step1Labels permutation12 permutation7
    mixedMoment B raw3613step2 raw3613step2Labels = mixedMoment B raw3613step3 raw3613step3Labels := by
      have ha : raw3613step3 = -raw3613step2 := by apply Matrix.ext; change ∀ i j, raw3613step3 i j = -(raw3613step2 i j); unfold raw3613step3 raw3613step2; decide +kernel
      have hl : raw3613step3Labels = raw3613step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3613step3 raw3613step3Labels = mixedMoment B raw3613step4 raw3613step4Labels := by
      have ha : raw3613step4 = raw3613step3 := by apply Matrix.ext; unfold raw3613step4 raw3613step3; decide +kernel
      have hl : raw3613step3Labels = labelEmbedding1 ∘ raw3613step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3613step3 raw3613step3Labels raw3613step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2279 node2279Labels := by rfl

def raw3614 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw3614Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3614step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw3614step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3614step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw3614step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3614step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -3, 3], ![-1, 1, 0], ![-2, 1, 1]]
def raw3614step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3614step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]
def raw3614step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3614step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]
def raw3614step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3614 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3614 raw3614Labels = mixedMoment B node1745 node1745Labels := by
  calc
    mixedMoment B raw3614 raw3614Labels = mixedMoment B raw3614step0 raw3614step0Labels := by
      have hz : ∀ j, raw3614 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3614step0 = (fun i j => raw3614 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3614step0 raw3614; decide +kernel
      have hl : raw3614step0Labels = raw3614Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3614 raw3614Labels permutation346 hz
    mixedMoment B raw3614step0 raw3614step0Labels = mixedMoment B raw3614step1 raw3614step1Labels := by
      have hz : ∀ j, raw3614step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3614step1 = (fun i j => raw3614step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3614step1 raw3614step0; decide +kernel
      have hl : raw3614step1Labels = raw3614step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3614step0 raw3614step0Labels permutation56 hz
    mixedMoment B raw3614step1 raw3614step1Labels = mixedMoment B raw3614step2 raw3614step2Labels := by
      have ha : raw3614step2 = (fun i j => raw3614step1 (permutation12 i) (permutation7 j)) := by apply Matrix.ext; unfold raw3614step2 raw3614step1; decide +kernel
      have hl : raw3614step2Labels = raw3614step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3614step1 raw3614step1Labels permutation12 permutation7
    mixedMoment B raw3614step2 raw3614step2Labels = mixedMoment B raw3614step3 raw3614step3Labels := by
      have ha : raw3614step3 = -raw3614step2 := by apply Matrix.ext; change ∀ i j, raw3614step3 i j = -(raw3614step2 i j); unfold raw3614step3 raw3614step2; decide +kernel
      have hl : raw3614step3Labels = raw3614step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3614step3 raw3614step3Labels = mixedMoment B raw3614step4 raw3614step4Labels := by
      have ha : raw3614step4 = raw3614step3 := by apply Matrix.ext; unfold raw3614step4 raw3614step3; decide +kernel
      have hl : raw3614step3Labels = labelEmbedding1 ∘ raw3614step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3614step3 raw3614step3Labels raw3614step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1745 node1745Labels := by rfl

def raw3615 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw3615Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3615step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw3615step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3615step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -3, 3], ![-1, 1, 0], ![-2, 1, 1]]
def raw3615step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3615step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]
def raw3615step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3615step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]
def raw3615step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3615 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3615 raw3615Labels = mixedMoment B node2220 node2220Labels := by
  calc
    mixedMoment B raw3615 raw3615Labels = mixedMoment B raw3615step0 raw3615step0Labels := by
      have hz : ∀ j, raw3615 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3615step0 = (fun i j => raw3615 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3615step0 raw3615; decide +kernel
      have hl : raw3615step0Labels = raw3615Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3615 raw3615Labels permutation346 hz
    mixedMoment B raw3615step0 raw3615step0Labels = mixedMoment B raw3615step1 raw3615step1Labels := by
      have ha : raw3615step1 = (fun i j => raw3615step0 (permutation36 i) (permutation7 j)) := by apply Matrix.ext; unfold raw3615step1 raw3615step0; decide +kernel
      have hl : raw3615step1Labels = raw3615step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3615step0 raw3615step0Labels permutation36 permutation7
    mixedMoment B raw3615step1 raw3615step1Labels = mixedMoment B raw3615step2 raw3615step2Labels := by
      have ha : raw3615step2 = -raw3615step1 := by apply Matrix.ext; change ∀ i j, raw3615step2 i j = -(raw3615step1 i j); unfold raw3615step2 raw3615step1; decide +kernel
      have hl : raw3615step2Labels = raw3615step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3615step2 raw3615step2Labels = mixedMoment B raw3615step3 raw3615step3Labels := by
      have ha : raw3615step3 = raw3615step2 := by apply Matrix.ext; unfold raw3615step3 raw3615step2; decide +kernel
      have hl : raw3615step2Labels = labelEmbedding1 ∘ raw3615step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3615step2 raw3615step2Labels raw3615step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2220 node2220Labels := by rfl

def raw3616 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw3616Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3616step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw3616step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3616step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -3, 3], ![-1, 1, 0], ![-2, 1, 1]]
def raw3616step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3616step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]
def raw3616step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3616step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]
def raw3616step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3616 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3616 raw3616Labels = mixedMoment B node2220 node2220Labels := by
  calc
    mixedMoment B raw3616 raw3616Labels = mixedMoment B raw3616step0 raw3616step0Labels := by
      have hz : ∀ j, raw3616 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3616step0 = (fun i j => raw3616 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3616step0 raw3616; decide +kernel
      have hl : raw3616step0Labels = raw3616Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3616 raw3616Labels permutation265 hz
    mixedMoment B raw3616step0 raw3616step0Labels = mixedMoment B raw3616step1 raw3616step1Labels := by
      have ha : raw3616step1 = (fun i j => raw3616step0 (permutation36 i) (permutation7 j)) := by apply Matrix.ext; unfold raw3616step1 raw3616step0; decide +kernel
      have hl : raw3616step1Labels = raw3616step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3616step0 raw3616step0Labels permutation36 permutation7
    mixedMoment B raw3616step1 raw3616step1Labels = mixedMoment B raw3616step2 raw3616step2Labels := by
      have ha : raw3616step2 = -raw3616step1 := by apply Matrix.ext; change ∀ i j, raw3616step2 i j = -(raw3616step1 i j); unfold raw3616step2 raw3616step1; decide +kernel
      have hl : raw3616step2Labels = raw3616step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3616step2 raw3616step2Labels = mixedMoment B raw3616step3 raw3616step3Labels := by
      have ha : raw3616step3 = raw3616step2 := by apply Matrix.ext; unfold raw3616step3 raw3616step2; decide +kernel
      have hl : raw3616step2Labels = labelEmbedding1 ∘ raw3616step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3616step2 raw3616step2Labels raw3616step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2220 node2220Labels := by rfl

def raw3617 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![1, 1, -2], ![3, -3, 0]]
def raw3617Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3617step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 2, -1], ![1, 1, -2], ![3, -3, 0]]
def raw3617step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3617step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 1, -2], ![3, -3, 0]]
def raw3617step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3617step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![1, -2, 1], ![2, -1, -1]]
def raw3617step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3617step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![1, -2, 1], ![2, -1, -1]]
def raw3617step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3617 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3617 raw3617Labels = mixedMoment B node2282 node2282Labels := by
  calc
    mixedMoment B raw3617 raw3617Labels = mixedMoment B raw3617step0 raw3617step0Labels := by
      have hz : ∀ j, raw3617 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3617step0 = (fun i j => raw3617 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3617step0 raw3617; decide +kernel
      have hl : raw3617step0Labels = raw3617Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3617 raw3617Labels permutation346 hz
    mixedMoment B raw3617step0 raw3617step0Labels = mixedMoment B raw3617step1 raw3617step1Labels := by
      have hz : ∀ j, raw3617step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3617step1 = (fun i j => raw3617step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3617step1 raw3617step0; decide +kernel
      have hl : raw3617step1Labels = raw3617step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3617step0 raw3617step0Labels permutation56 hz
    mixedMoment B raw3617step1 raw3617step1Labels = mixedMoment B raw3617step2 raw3617step2Labels := by
      have ha : raw3617step2 = (fun i j => raw3617step1 (permutation27 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3617step2 raw3617step1; decide +kernel
      have hl : raw3617step2Labels = raw3617step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3617step1 raw3617step1Labels permutation27 permutation5
    mixedMoment B raw3617step2 raw3617step2Labels = mixedMoment B raw3617step3 raw3617step3Labels := by
      have ha : raw3617step3 = raw3617step2 := by apply Matrix.ext; unfold raw3617step3 raw3617step2; decide +kernel
      have hl : raw3617step2Labels = labelEmbedding1 ∘ raw3617step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3617step2 raw3617step2Labels raw3617step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2282 node2282Labels := by rfl

def raw3618 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw3618Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3618step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw3618step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3618step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw3618step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3618step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw3618step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3618step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw3618step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3618step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw3618step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3618 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3618 raw3618Labels = mixedMoment B node2278 node2278Labels := by
  calc
    mixedMoment B raw3618 raw3618Labels = mixedMoment B raw3618step0 raw3618step0Labels := by
      have hz : ∀ j, raw3618 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3618step0 = (fun i j => raw3618 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3618step0 raw3618; decide +kernel
      have hl : raw3618step0Labels = raw3618Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3618 raw3618Labels permutation346 hz
    mixedMoment B raw3618step0 raw3618step0Labels = mixedMoment B raw3618step1 raw3618step1Labels := by
      have hz : ∀ j, raw3618step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3618step1 = (fun i j => raw3618step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3618step1 raw3618step0; decide +kernel
      have hl : raw3618step1Labels = raw3618step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3618step0 raw3618step0Labels permutation56 hz
    mixedMoment B raw3618step1 raw3618step1Labels = mixedMoment B raw3618step2 raw3618step2Labels := by
      have ha : raw3618step2 = (fun i j => raw3618step1 (permutation12 i) (permutation7 j)) := by apply Matrix.ext; unfold raw3618step2 raw3618step1; decide +kernel
      have hl : raw3618step2Labels = raw3618step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3618step1 raw3618step1Labels permutation12 permutation7
    mixedMoment B raw3618step2 raw3618step2Labels = mixedMoment B raw3618step3 raw3618step3Labels := by
      have ha : raw3618step3 = -raw3618step2 := by apply Matrix.ext; change ∀ i j, raw3618step3 i j = -(raw3618step2 i j); unfold raw3618step3 raw3618step2; decide +kernel
      have hl : raw3618step3Labels = raw3618step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3618step3 raw3618step3Labels = mixedMoment B raw3618step4 raw3618step4Labels := by
      have ha : raw3618step4 = raw3618step3 := by apply Matrix.ext; unfold raw3618step4 raw3618step3; decide +kernel
      have hl : raw3618step3Labels = labelEmbedding1 ∘ raw3618step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3618step3 raw3618step3Labels raw3618step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2278 node2278Labels := by rfl

def raw3619 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2], ![4, -4, 0]]
def raw3619Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3619step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2], ![4, -4, 0]]
def raw3619step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3619step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 2, -2], ![4, -4, 0]]
def raw3619step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3619step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, 3, -4], ![2, -2, 0]]
def raw3619step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3619step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, 3, -4], ![2, -2, 0]]
def raw3619step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3619 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3619 raw3619Labels = mixedMoment B node854 node854Labels := by
  calc
    mixedMoment B raw3619 raw3619Labels = mixedMoment B raw3619step0 raw3619step0Labels := by
      have hz : ∀ j, raw3619 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3619step0 = (fun i j => raw3619 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3619step0 raw3619; decide +kernel
      have hl : raw3619step0Labels = raw3619Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3619 raw3619Labels permutation346 hz
    mixedMoment B raw3619step0 raw3619step0Labels = mixedMoment B raw3619step1 raw3619step1Labels := by
      have hz : ∀ j, raw3619step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3619step1 = (fun i j => raw3619step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3619step1 raw3619step0; decide +kernel
      have hl : raw3619step1Labels = raw3619step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3619step0 raw3619step0Labels permutation56 hz
    mixedMoment B raw3619step1 raw3619step1Labels = mixedMoment B raw3619step2 raw3619step2Labels := by
      have ha : raw3619step2 = (fun i j => raw3619step1 (permutation28 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3619step2 raw3619step1; decide +kernel
      have hl : raw3619step2Labels = raw3619step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3619step1 raw3619step1Labels permutation28 permutation5
    mixedMoment B raw3619step2 raw3619step2Labels = mixedMoment B raw3619step3 raw3619step3Labels := by
      have ha : raw3619step3 = raw3619step2 := by apply Matrix.ext; unfold raw3619step3 raw3619step2; decide +kernel
      have hl : raw3619step2Labels = labelEmbedding1 ∘ raw3619step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3619step2 raw3619step2Labels raw3619step3Labels labelEmbedding1 hl
    _ = mixedMoment B node854 node854Labels := by rfl

def raw3620 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2], ![4, -4, 0]]
def raw3620Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3620step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2], ![4, -4, 0]]
def raw3620step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3620step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw3620step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3620step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw3620step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3620 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3620 raw3620Labels = mixedMoment B node835 node835Labels := by
  calc
    mixedMoment B raw3620 raw3620Labels = mixedMoment B raw3620step0 raw3620step0Labels := by
      have hz : ∀ j, raw3620 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3620step0 = (fun i j => raw3620 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3620step0 raw3620; decide +kernel
      have hl : raw3620step0Labels = raw3620Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3620 raw3620Labels permutation346 hz
    mixedMoment B raw3620step0 raw3620step0Labels = mixedMoment B raw3620step1 raw3620step1Labels := by
      have ha : raw3620step1 = (fun i j => raw3620step0 (permutation130 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3620step1 raw3620step0; decide +kernel
      have hl : raw3620step1Labels = raw3620step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3620step0 raw3620step0Labels permutation130 permutation5
    mixedMoment B raw3620step1 raw3620step1Labels = mixedMoment B raw3620step2 raw3620step2Labels := by
      have ha : raw3620step2 = raw3620step1 := by apply Matrix.ext; unfold raw3620step2 raw3620step1; decide +kernel
      have hl : raw3620step1Labels = labelEmbedding1 ∘ raw3620step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3620step1 raw3620step1Labels raw3620step2Labels labelEmbedding1 hl
    _ = mixedMoment B node835 node835Labels := by rfl

def raw3621 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2], ![4, -4, 0]]
def raw3621Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3621step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2], ![4, -4, 0]]
def raw3621step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3621step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw3621step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3621step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw3621step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3621 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3621 raw3621Labels = mixedMoment B node835 node835Labels := by
  calc
    mixedMoment B raw3621 raw3621Labels = mixedMoment B raw3621step0 raw3621step0Labels := by
      have hz : ∀ j, raw3621 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3621step0 = (fun i j => raw3621 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3621step0 raw3621; decide +kernel
      have hl : raw3621step0Labels = raw3621Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3621 raw3621Labels permutation265 hz
    mixedMoment B raw3621step0 raw3621step0Labels = mixedMoment B raw3621step1 raw3621step1Labels := by
      have ha : raw3621step1 = (fun i j => raw3621step0 (permutation130 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3621step1 raw3621step0; decide +kernel
      have hl : raw3621step1Labels = raw3621step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3621step0 raw3621step0Labels permutation130 permutation5
    mixedMoment B raw3621step1 raw3621step1Labels = mixedMoment B raw3621step2 raw3621step2Labels := by
      have ha : raw3621step2 = raw3621step1 := by apply Matrix.ext; unfold raw3621step2 raw3621step1; decide +kernel
      have hl : raw3621step1Labels = labelEmbedding1 ∘ raw3621step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3621step1 raw3621step1Labels raw3621step2Labels labelEmbedding1 hl
    _ = mixedMoment B node835 node835Labels := by rfl

def raw3622 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![0, 2, -2], ![4, -4, 0]]
def raw3622Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3622step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 2, -1], ![0, 2, -2], ![4, -4, 0]]
def raw3622step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3622step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 2, -2], ![4, -4, 0]]
def raw3622step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3622step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 3, -3], ![2, -2, 0], ![2, -1, -1]]
def raw3622step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3622step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 3, -3], ![2, -2, 0], ![2, -1, -1]]
def raw3622step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3622 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3622 raw3622Labels = mixedMoment B node838 node838Labels := by
  calc
    mixedMoment B raw3622 raw3622Labels = mixedMoment B raw3622step0 raw3622step0Labels := by
      have hz : ∀ j, raw3622 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3622step0 = (fun i j => raw3622 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3622step0 raw3622; decide +kernel
      have hl : raw3622step0Labels = raw3622Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3622 raw3622Labels permutation346 hz
    mixedMoment B raw3622step0 raw3622step0Labels = mixedMoment B raw3622step1 raw3622step1Labels := by
      have hz : ∀ j, raw3622step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3622step1 = (fun i j => raw3622step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3622step1 raw3622step0; decide +kernel
      have hl : raw3622step1Labels = raw3622step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3622step0 raw3622step0Labels permutation56 hz
    mixedMoment B raw3622step1 raw3622step1Labels = mixedMoment B raw3622step2 raw3622step2Labels := by
      have ha : raw3622step2 = (fun i j => raw3622step1 (permutation27 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3622step2 raw3622step1; decide +kernel
      have hl : raw3622step2Labels = raw3622step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3622step1 raw3622step1Labels permutation27 permutation5
    mixedMoment B raw3622step2 raw3622step2Labels = mixedMoment B raw3622step3 raw3622step3Labels := by
      have ha : raw3622step3 = raw3622step2 := by apply Matrix.ext; unfold raw3622step3 raw3622step2; decide +kernel
      have hl : raw3622step2Labels = labelEmbedding1 ∘ raw3622step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3622step2 raw3622step2Labels raw3622step3Labels labelEmbedding1 hl
    _ = mixedMoment B node838 node838Labels := by rfl

def raw3623 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![-1, 3, -2], ![4, -4, 0]]
def raw3623Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3623step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![-1, 3, -2], ![4, -4, 0]]
def raw3623step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3623step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 3, -2], ![4, -4, 0]]
def raw3623step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3623step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 3, -3], ![1, -1, 0], ![3, -2, -1]]
def raw3623step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3623step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 3, -3], ![1, -1, 0], ![3, -2, -1]]
def raw3623step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3623 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3623 raw3623Labels = mixedMoment B node836 node836Labels := by
  calc
    mixedMoment B raw3623 raw3623Labels = mixedMoment B raw3623step0 raw3623step0Labels := by
      have hz : ∀ j, raw3623 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3623step0 = (fun i j => raw3623 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3623step0 raw3623; decide +kernel
      have hl : raw3623step0Labels = raw3623Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3623 raw3623Labels permutation346 hz
    mixedMoment B raw3623step0 raw3623step0Labels = mixedMoment B raw3623step1 raw3623step1Labels := by
      have hz : ∀ j, raw3623step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3623step1 = (fun i j => raw3623step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3623step1 raw3623step0; decide +kernel
      have hl : raw3623step1Labels = raw3623step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3623step0 raw3623step0Labels permutation56 hz
    mixedMoment B raw3623step1 raw3623step1Labels = mixedMoment B raw3623step2 raw3623step2Labels := by
      have ha : raw3623step2 = (fun i j => raw3623step1 (permutation26 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3623step2 raw3623step1; decide +kernel
      have hl : raw3623step2Labels = raw3623step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3623step1 raw3623step1Labels permutation26 permutation5
    mixedMoment B raw3623step2 raw3623step2Labels = mixedMoment B raw3623step3 raw3623step3Labels := by
      have ha : raw3623step3 = raw3623step2 := by apply Matrix.ext; unfold raw3623step3 raw3623step2; decide +kernel
      have hl : raw3623step2Labels = labelEmbedding1 ∘ raw3623step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3623step2 raw3623step2Labels raw3623step3Labels labelEmbedding1 hl
    _ = mixedMoment B node836 node836Labels := by rfl

def raw3624 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3624Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3624step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3624step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3624step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3624step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3624 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3624 raw3624Labels = mixedMoment B node2255 node2255Labels := by
  calc
    mixedMoment B raw3624 raw3624Labels = mixedMoment B raw3624step0 raw3624step0Labels := by
      have hz : ∀ j, raw3624 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3624step0 = (fun i j => raw3624 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3624step0 raw3624; decide +kernel
      have hl : raw3624step0Labels = raw3624Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3624 raw3624Labels permutation346 hz
    mixedMoment B raw3624step0 raw3624step0Labels = mixedMoment B raw3624step1 raw3624step1Labels := by
      have hz : ∀ j, raw3624step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3624step1 = (fun i j => raw3624step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3624step1 raw3624step0; decide +kernel
      have hl : raw3624step1Labels = raw3624step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3624step0 raw3624step0Labels permutation56 hz
    _ = mixedMoment B node2255 node2255Labels := by rfl

def raw3625 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3625Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3625step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3625step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3625step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw3625step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3625 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3625 raw3625Labels = mixedMoment B node3156 node3156Labels := by
  calc
    mixedMoment B raw3625 raw3625Labels = mixedMoment B raw3625step0 raw3625step0Labels := by
      have hz : ∀ j, raw3625 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3625step0 = (fun i j => raw3625 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3625step0 raw3625; decide +kernel
      have hl : raw3625step0Labels = raw3625Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3625 raw3625Labels permutation346 hz
    mixedMoment B raw3625step0 raw3625step0Labels = mixedMoment B raw3625step1 raw3625step1Labels := by
      have ha : raw3625step1 = (fun i j => raw3625step0 (permutation128 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3625step1 raw3625step0; decide +kernel
      have hl : raw3625step1Labels = raw3625step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3625step0 raw3625step0Labels permutation128 permutation4
    _ = mixedMoment B node3156 node3156Labels := by rfl

def raw3626 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3626Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3626step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3626step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3626step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw3626step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3626 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3626 raw3626Labels = mixedMoment B node3156 node3156Labels := by
  calc
    mixedMoment B raw3626 raw3626Labels = mixedMoment B raw3626step0 raw3626step0Labels := by
      have hz : ∀ j, raw3626 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3626step0 = (fun i j => raw3626 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3626step0 raw3626; decide +kernel
      have hl : raw3626step0Labels = raw3626Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3626 raw3626Labels permutation265 hz
    mixedMoment B raw3626step0 raw3626step0Labels = mixedMoment B raw3626step1 raw3626step1Labels := by
      have ha : raw3626step1 = (fun i j => raw3626step0 (permutation128 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3626step1 raw3626step0; decide +kernel
      have hl : raw3626step1Labels = raw3626step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3626step0 raw3626step0Labels permutation128 permutation4
    _ = mixedMoment B node3156 node3156Labels := by rfl

def raw3627 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3627Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3627step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![-1, 2, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3627step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3627step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3627step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3627step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![2, -1, -1], ![2, 0, -2]]
def raw3627step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3627 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3627 raw3627Labels = mixedMoment B node3161 node3161Labels := by
  calc
    mixedMoment B raw3627 raw3627Labels = mixedMoment B raw3627step0 raw3627step0Labels := by
      have hz : ∀ j, raw3627 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3627step0 = (fun i j => raw3627 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3627step0 raw3627; decide +kernel
      have hl : raw3627step0Labels = raw3627Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3627 raw3627Labels permutation346 hz
    mixedMoment B raw3627step0 raw3627step0Labels = mixedMoment B raw3627step1 raw3627step1Labels := by
      have hz : ∀ j, raw3627step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3627step1 = (fun i j => raw3627step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3627step1 raw3627step0; decide +kernel
      have hl : raw3627step1Labels = raw3627step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3627step0 raw3627step0Labels permutation56 hz
    mixedMoment B raw3627step1 raw3627step1Labels = mixedMoment B raw3627step2 raw3627step2Labels := by
      have ha : raw3627step2 = (fun i j => raw3627step1 (permutation26 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3627step2 raw3627step1; decide +kernel
      have hl : raw3627step2Labels = raw3627step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3627step1 raw3627step1Labels permutation26 permutation4
    _ = mixedMoment B node3161 node3161Labels := by rfl

def raw3628 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![-1, 3, -2], ![3, -3, 0]]
def raw3628Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3628step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 1, -1], ![-1, 3, -2], ![3, -3, 0]]
def raw3628step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3628step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![-1, 3, -2], ![3, -3, 0]]
def raw3628step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3628step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![-1, -2, 3], ![-3, 3, 0]]
def raw3628step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3628step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 2, -3], ![3, -3, 0]]
def raw3628step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3628 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3628 raw3628Labels = mixedMoment B node2520 node2520Labels := by
  calc
    mixedMoment B raw3628 raw3628Labels = mixedMoment B raw3628step0 raw3628step0Labels := by
      have hz : ∀ j, raw3628 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3628step0 = (fun i j => raw3628 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3628step0 raw3628; decide +kernel
      have hl : raw3628step0Labels = raw3628Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3628 raw3628Labels permutation346 hz
    mixedMoment B raw3628step0 raw3628step0Labels = mixedMoment B raw3628step1 raw3628step1Labels := by
      have hz : ∀ j, raw3628step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3628step1 = (fun i j => raw3628step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3628step1 raw3628step0; decide +kernel
      have hl : raw3628step1Labels = raw3628step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3628step0 raw3628step0Labels permutation56 hz
    mixedMoment B raw3628step1 raw3628step1Labels = mixedMoment B raw3628step2 raw3628step2Labels := by
      have ha : raw3628step2 = (fun i j => raw3628step1 (permutation22 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3628step2 raw3628step1; decide +kernel
      have hl : raw3628step2Labels = raw3628step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3628step1 raw3628step1Labels permutation22 permutation4
    mixedMoment B raw3628step2 raw3628step2Labels = mixedMoment B raw3628step3 raw3628step3Labels := by
      have ha : raw3628step3 = -raw3628step2 := by apply Matrix.ext; change ∀ i j, raw3628step3 i j = -(raw3628step2 i j); unfold raw3628step3 raw3628step2; decide +kernel
      have hl : raw3628step3Labels = raw3628step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2520 node2520Labels := by rfl

def raw3629 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw3629Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3629step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw3629step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3629step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw3629step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3629 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3629 raw3629Labels = mixedMoment B node3626 node3626Labels := by
  calc
    mixedMoment B raw3629 raw3629Labels = mixedMoment B raw3629step0 raw3629step0Labels := by
      have hz : ∀ j, raw3629 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3629step0 = (fun i j => raw3629 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3629step0 raw3629; decide +kernel
      have hl : raw3629step0Labels = raw3629Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3629 raw3629Labels permutation346 hz
    mixedMoment B raw3629step0 raw3629step0Labels = mixedMoment B raw3629step1 raw3629step1Labels := by
      have hz : ∀ j, raw3629step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3629step1 = (fun i j => raw3629step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3629step1 raw3629step0; decide +kernel
      have hl : raw3629step1Labels = raw3629step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3629step0 raw3629step0Labels permutation56 hz
    _ = mixedMoment B node3626 node3626Labels := by rfl

def raw3630 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![0, 0], ![1, -1], ![2, -2], ![0, 0]]
def raw3630Labels : Fin 2 → Fin 2 := ![0, 1]

def raw3630step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![0, 0], ![1, -1], ![2, -2]]
def raw3630step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw3630step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![1, -1], ![2, -2]]
def raw3630step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw3630step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]
def raw3630step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical3630 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3630 raw3630Labels = mixedMoment B node4084 node4084Labels := by
  calc
    mixedMoment B raw3630 raw3630Labels = mixedMoment B raw3630step0 raw3630step0Labels := by
      have hz : ∀ j, raw3630 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw3630step0 = (fun i j => raw3630 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw3630step0 raw3630; decide +kernel
      have hl : raw3630step0Labels = raw3630Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3630 raw3630Labels permutation590 hz
    mixedMoment B raw3630step0 raw3630step0Labels = mixedMoment B raw3630step1 raw3630step1Labels := by
      have hz : ∀ j, raw3630step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3630step1 = (fun i j => raw3630step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3630step1 raw3630step0; decide +kernel
      have hl : raw3630step1Labels = raw3630step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3630step0 raw3630step0Labels permutation80 hz
    mixedMoment B raw3630step1 raw3630step1Labels = mixedMoment B raw3630step2 raw3630step2Labels := by
      have hz : ∀ j, raw3630step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw3630step2 = (fun i j => raw3630step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw3630step2 raw3630step1; decide +kernel
      have hl : raw3630step2Labels = raw3630step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3630step1 raw3630step1Labels permutation14 hz
    _ = mixedMoment B node4084 node4084Labels := by rfl

def raw3631 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3631Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3631step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3631step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3631step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![3, -3, 0]]
def raw3631step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3631 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3631 raw3631Labels = mixedMoment B node1029 node1029Labels := by
  calc
    mixedMoment B raw3631 raw3631Labels = mixedMoment B raw3631step0 raw3631step0Labels := by
      have hz : ∀ j, raw3631 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3631step0 = (fun i j => raw3631 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3631step0 raw3631; decide +kernel
      have hl : raw3631step0Labels = raw3631Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3631 raw3631Labels permutation346 hz
    mixedMoment B raw3631step0 raw3631step0Labels = mixedMoment B raw3631step1 raw3631step1Labels := by
      have ha : raw3631step1 = (fun i j => raw3631step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3631step1 raw3631step0; decide +kernel
      have hl : raw3631step1Labels = raw3631step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3631step0 raw3631step0Labels permutation40 permutation2
    _ = mixedMoment B node1029 node1029Labels := by rfl

def raw3632 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3632Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3632step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3632step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3632step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![3, -3, 0]]
def raw3632step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3632 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3632 raw3632Labels = mixedMoment B node1029 node1029Labels := by
  calc
    mixedMoment B raw3632 raw3632Labels = mixedMoment B raw3632step0 raw3632step0Labels := by
      have hz : ∀ j, raw3632 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3632step0 = (fun i j => raw3632 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3632step0 raw3632; decide +kernel
      have hl : raw3632step0Labels = raw3632Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3632 raw3632Labels permutation265 hz
    mixedMoment B raw3632step0 raw3632step0Labels = mixedMoment B raw3632step1 raw3632step1Labels := by
      have ha : raw3632step1 = (fun i j => raw3632step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3632step1 raw3632step0; decide +kernel
      have hl : raw3632step1Labels = raw3632step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3632step0 raw3632step0Labels permutation40 permutation2
    _ = mixedMoment B node1029 node1029Labels := by rfl

def raw3633 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3633Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3633step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 0, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3633step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3633step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3633step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3633step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw3633step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3633 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3633 raw3633Labels = mixedMoment B node1061 node1061Labels := by
  calc
    mixedMoment B raw3633 raw3633Labels = mixedMoment B raw3633step0 raw3633step0Labels := by
      have hz : ∀ j, raw3633 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3633step0 = (fun i j => raw3633 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3633step0 raw3633; decide +kernel
      have hl : raw3633step0Labels = raw3633Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3633 raw3633Labels permutation346 hz
    mixedMoment B raw3633step0 raw3633step0Labels = mixedMoment B raw3633step1 raw3633step1Labels := by
      have hz : ∀ j, raw3633step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3633step1 = (fun i j => raw3633step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3633step1 raw3633step0; decide +kernel
      have hl : raw3633step1Labels = raw3633step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3633step0 raw3633step0Labels permutation56 hz
    mixedMoment B raw3633step1 raw3633step1Labels = mixedMoment B raw3633step2 raw3633step2Labels := by
      have ha : raw3633step2 = (fun i j => raw3633step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3633step2 raw3633step1; decide +kernel
      have hl : raw3633step2Labels = raw3633step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3633step1 raw3633step1Labels permutation10 permutation2
    _ = mixedMoment B node1061 node1061Labels := by rfl

def raw3634 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw3634Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3634step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw3634step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3634step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw3634step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3634 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3634 raw3634Labels = mixedMoment B node1047 node1047Labels := by
  calc
    mixedMoment B raw3634 raw3634Labels = mixedMoment B raw3634step0 raw3634step0Labels := by
      have hz : ∀ j, raw3634 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3634step0 = (fun i j => raw3634 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3634step0 raw3634; decide +kernel
      have hl : raw3634step0Labels = raw3634Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3634 raw3634Labels permutation346 hz
    mixedMoment B raw3634step0 raw3634step0Labels = mixedMoment B raw3634step1 raw3634step1Labels := by
      have hz : ∀ j, raw3634step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3634step1 = (fun i j => raw3634step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3634step1 raw3634step0; decide +kernel
      have hl : raw3634step1Labels = raw3634step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3634step0 raw3634step0Labels permutation56 hz
    _ = mixedMoment B node1047 node1047Labels := by rfl

def raw3635 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2], ![4, -4, 0]]
def raw3635Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3635step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2], ![4, -4, 0]]
def raw3635step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3635step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 2, -2], ![4, -4, 0]]
def raw3635step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3635 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3635 raw3635Labels = mixedMoment B node1031 node1031Labels := by
  calc
    mixedMoment B raw3635 raw3635Labels = mixedMoment B raw3635step0 raw3635step0Labels := by
      have hz : ∀ j, raw3635 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3635step0 = (fun i j => raw3635 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3635step0 raw3635; decide +kernel
      have hl : raw3635step0Labels = raw3635Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3635 raw3635Labels permutation346 hz
    mixedMoment B raw3635step0 raw3635step0Labels = mixedMoment B raw3635step1 raw3635step1Labels := by
      have hz : ∀ j, raw3635step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3635step1 = (fun i j => raw3635step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3635step1 raw3635step0; decide +kernel
      have hl : raw3635step1Labels = raw3635step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3635step0 raw3635step0Labels permutation56 hz
    _ = mixedMoment B node1031 node1031Labels := by rfl

def raw3636 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3636Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3636step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![3, -3, 0]]
def raw3636step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3636 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3636 raw3636Labels = mixedMoment B node2013 node2013Labels := by
  calc
    mixedMoment B raw3636 raw3636Labels = mixedMoment B raw3636step0 raw3636step0Labels := by
      have ha : raw3636step0 = (fun i j => raw3636 (permutation184 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3636step0 raw3636; decide +kernel
      have hl : raw3636step0Labels = raw3636Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3636 raw3636Labels permutation184 permutation2
    _ = mixedMoment B node2013 node2013Labels := by rfl

def raw3637 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![0, 0, 0], ![-1, 2, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3637Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3637step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![-1, 2, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3637step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3637step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 2, -2], ![1, -1, 0], ![3, -3, 0]]
def raw3637step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3637 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3637 raw3637Labels = mixedMoment B node2096 node2096Labels := by
  calc
    mixedMoment B raw3637 raw3637Labels = mixedMoment B raw3637step0 raw3637step0Labels := by
      have hz : ∀ j, raw3637 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3637step0 = (fun i j => raw3637 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3637step0 raw3637; decide +kernel
      have hl : raw3637step0Labels = raw3637Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3637 raw3637Labels permutation346 hz
    mixedMoment B raw3637step0 raw3637step0Labels = mixedMoment B raw3637step1 raw3637step1Labels := by
      have ha : raw3637step1 = (fun i j => raw3637step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3637step1 raw3637step0; decide +kernel
      have hl : raw3637step1Labels = raw3637step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3637step0 raw3637step0Labels permutation40 permutation2
    _ = mixedMoment B node2096 node2096Labels := by rfl

def raw3638 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![-1, 3, -2], ![3, -3, 0]]
def raw3638Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3638step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![0, 1, -1], ![-1, 3, -2], ![3, -3, 0]]
def raw3638step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3638step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, 1, -1], ![1, -1, 0], ![3, -3, 0]]
def raw3638step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3638 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3638 raw3638Labels = mixedMoment B node2125 node2125Labels := by
  calc
    mixedMoment B raw3638 raw3638Labels = mixedMoment B raw3638step0 raw3638step0Labels := by
      have hz : ∀ j, raw3638 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3638step0 = (fun i j => raw3638 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3638step0 raw3638; decide +kernel
      have hl : raw3638step0Labels = raw3638Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3638 raw3638Labels permutation346 hz
    mixedMoment B raw3638step0 raw3638step0Labels = mixedMoment B raw3638step1 raw3638step1Labels := by
      have ha : raw3638step1 = (fun i j => raw3638step0 (permutation46 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3638step1 raw3638step0; decide +kernel
      have hl : raw3638step1Labels = raw3638step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3638step0 raw3638step0Labels permutation46 permutation2
    _ = mixedMoment B node2125 node2125Labels := by rfl

def raw3639 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw3639Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3639step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw3639step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3639step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw3639step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3639 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3639 raw3639Labels = mixedMoment B node2253 node2253Labels := by
  calc
    mixedMoment B raw3639 raw3639Labels = mixedMoment B raw3639step0 raw3639step0Labels := by
      have hz : ∀ j, raw3639 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3639step0 = (fun i j => raw3639 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3639step0 raw3639; decide +kernel
      have hl : raw3639step0Labels = raw3639Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3639 raw3639Labels permutation346 hz
    mixedMoment B raw3639step0 raw3639step0Labels = mixedMoment B raw3639step1 raw3639step1Labels := by
      have ha : raw3639step1 = (fun i j => raw3639step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3639step1 raw3639step0; decide +kernel
      have hl : raw3639step1Labels = raw3639step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3639step0 raw3639step0Labels permutation40 permutation2
    _ = mixedMoment B node2253 node2253Labels := by rfl

def raw3640 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3640Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3640step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![3, -3, 0]]
def raw3640step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3640 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3640 raw3640Labels = mixedMoment B node2013 node2013Labels := by
  calc
    mixedMoment B raw3640 raw3640Labels = mixedMoment B raw3640step0 raw3640step0Labels := by
      have ha : raw3640step0 = (fun i j => raw3640 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3640step0 raw3640; decide +kernel
      have hl : raw3640step0Labels = raw3640Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3640 raw3640Labels permutation160 permutation2
    _ = mixedMoment B node2013 node2013Labels := by rfl

def raw3641 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3641Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3641step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3641step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3641step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw3641step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3641 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3641 raw3641Labels = mixedMoment B node2037 node2037Labels := by
  calc
    mixedMoment B raw3641 raw3641Labels = mixedMoment B raw3641step0 raw3641step0Labels := by
      have hz : ∀ j, raw3641 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3641step0 = (fun i j => raw3641 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3641step0 raw3641; decide +kernel
      have hl : raw3641step0Labels = raw3641Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3641 raw3641Labels permutation346 hz
    mixedMoment B raw3641step0 raw3641step0Labels = mixedMoment B raw3641step1 raw3641step1Labels := by
      have ha : raw3641step1 = (fun i j => raw3641step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3641step1 raw3641step0; decide +kernel
      have hl : raw3641step1Labels = raw3641step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3641step0 raw3641step0Labels permutation34 permutation2
    _ = mixedMoment B node2037 node2037Labels := by rfl

def raw3642 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw3642Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3642step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw3642step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3642 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3642 raw3642Labels = mixedMoment B node2026 node2026Labels := by
  calc
    mixedMoment B raw3642 raw3642Labels = mixedMoment B raw3642step0 raw3642step0Labels := by
      have hz : ∀ j, raw3642 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3642step0 = (fun i j => raw3642 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3642step0 raw3642; decide +kernel
      have hl : raw3642step0Labels = raw3642Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3642 raw3642Labels permutation346 hz
    _ = mixedMoment B node2026 node2026Labels := by rfl

def raw3643 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2], ![4, -4, 0]]
def raw3643Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3643step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2], ![4, -4, 0]]
def raw3643step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3643step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -3, 3], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw3643step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3643 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3643 raw3643Labels = mixedMoment B node1458 node1458Labels := by
  calc
    mixedMoment B raw3643 raw3643Labels = mixedMoment B raw3643step0 raw3643step0Labels := by
      have hz : ∀ j, raw3643 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3643step0 = (fun i j => raw3643 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3643step0 raw3643; decide +kernel
      have hl : raw3643step0Labels = raw3643Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3643 raw3643Labels permutation346 hz
    mixedMoment B raw3643step0 raw3643step0Labels = mixedMoment B raw3643step1 raw3643step1Labels := by
      have ha : raw3643step1 = (fun i j => raw3643step0 (permutation128 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3643step1 raw3643step0; decide +kernel
      have hl : raw3643step1Labels = raw3643step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3643step0 raw3643step0Labels permutation128 permutation4
    _ = mixedMoment B node1458 node1458Labels := by rfl

def raw3644 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3644Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3644step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3644step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3644step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw3644step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3644 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3644 raw3644Labels = mixedMoment B node2037 node2037Labels := by
  calc
    mixedMoment B raw3644 raw3644Labels = mixedMoment B raw3644step0 raw3644step0Labels := by
      have hz : ∀ j, raw3644 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3644step0 = (fun i j => raw3644 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3644step0 raw3644; decide +kernel
      have hl : raw3644step0Labels = raw3644Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3644 raw3644Labels permutation265 hz
    mixedMoment B raw3644step0 raw3644step0Labels = mixedMoment B raw3644step1 raw3644step1Labels := by
      have ha : raw3644step1 = (fun i j => raw3644step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3644step1 raw3644step0; decide +kernel
      have hl : raw3644step1Labels = raw3644step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3644step0 raw3644step0Labels permutation34 permutation2
    _ = mixedMoment B node2037 node2037Labels := by rfl

def raw3645 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![-1, 3, -2], ![3, -3, 0]]
def raw3645Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3645step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 0, -1], ![-1, 3, -2], ![3, -3, 0]]
def raw3645step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3645step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![-1, 3, -2], ![3, -3, 0]]
def raw3645step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3645step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, 0, -1], ![3, -3, 0]]
def raw3645step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3645 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3645 raw3645Labels = mixedMoment B node2136 node2136Labels := by
  calc
    mixedMoment B raw3645 raw3645Labels = mixedMoment B raw3645step0 raw3645step0Labels := by
      have hz : ∀ j, raw3645 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3645step0 = (fun i j => raw3645 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3645step0 raw3645; decide +kernel
      have hl : raw3645step0Labels = raw3645Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3645 raw3645Labels permutation346 hz
    mixedMoment B raw3645step0 raw3645step0Labels = mixedMoment B raw3645step1 raw3645step1Labels := by
      have hz : ∀ j, raw3645step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3645step1 = (fun i j => raw3645step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3645step1 raw3645step0; decide +kernel
      have hl : raw3645step1Labels = raw3645step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3645step0 raw3645step0Labels permutation56 hz
    mixedMoment B raw3645step1 raw3645step1Labels = mixedMoment B raw3645step2 raw3645step2Labels := by
      have ha : raw3645step2 = (fun i j => raw3645step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3645step2 raw3645step1; decide +kernel
      have hl : raw3645step2Labels = raw3645step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3645step1 raw3645step1Labels permutation10 permutation2
    _ = mixedMoment B node2136 node2136Labels := by rfl

def raw3646 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![0, 2, -2], ![2, -2, 0]]
def raw3646Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3646step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 0, -1], ![0, 2, -2], ![2, -2, 0]]
def raw3646step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3646step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 2, -2], ![2, -2, 0]]
def raw3646step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3646step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw3646step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3646 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3646 raw3646Labels = mixedMoment B node2279 node2279Labels := by
  calc
    mixedMoment B raw3646 raw3646Labels = mixedMoment B raw3646step0 raw3646step0Labels := by
      have hz : ∀ j, raw3646 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3646step0 = (fun i j => raw3646 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3646step0 raw3646; decide +kernel
      have hl : raw3646step0Labels = raw3646Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3646 raw3646Labels permutation346 hz
    mixedMoment B raw3646step0 raw3646step0Labels = mixedMoment B raw3646step1 raw3646step1Labels := by
      have hz : ∀ j, raw3646step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3646step1 = (fun i j => raw3646step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3646step1 raw3646step0; decide +kernel
      have hl : raw3646step1Labels = raw3646step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3646step0 raw3646step0Labels permutation56 hz
    mixedMoment B raw3646step1 raw3646step1Labels = mixedMoment B raw3646step2 raw3646step2Labels := by
      have ha : raw3646step2 = (fun i j => raw3646step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3646step2 raw3646step1; decide +kernel
      have hl : raw3646step2Labels = raw3646step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3646step1 raw3646step1Labels permutation10 permutation2
    _ = mixedMoment B node2279 node2279Labels := by rfl

def raw3647 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, -1, 0], ![-1, 2, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3647Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3647step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![-1, 2, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3647step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3647step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 2, -2], ![1, -1, 0], ![3, -3, 0]]
def raw3647step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3647 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3647 raw3647Labels = mixedMoment B node2096 node2096Labels := by
  calc
    mixedMoment B raw3647 raw3647Labels = mixedMoment B raw3647step0 raw3647step0Labels := by
      have hz : ∀ j, raw3647 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3647step0 = (fun i j => raw3647 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3647step0 raw3647; decide +kernel
      have hl : raw3647step0Labels = raw3647Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3647 raw3647Labels permutation265 hz
    mixedMoment B raw3647step0 raw3647step0Labels = mixedMoment B raw3647step1 raw3647step1Labels := by
      have ha : raw3647step1 = (fun i j => raw3647step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3647step1 raw3647step0; decide +kernel
      have hl : raw3647step1Labels = raw3647step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3647step0 raw3647step0Labels permutation40 permutation2
    _ = mixedMoment B node2096 node2096Labels := by rfl

def raw3648 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![1, 1, -2], ![3, -3, 0]]
def raw3648Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3648step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 2, -1], ![1, 1, -2], ![3, -3, 0]]
def raw3648step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3648step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 1, -2], ![3, -3, 0]]
def raw3648step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3648 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3648 raw3648Labels = mixedMoment B node2113 node2113Labels := by
  calc
    mixedMoment B raw3648 raw3648Labels = mixedMoment B raw3648step0 raw3648step0Labels := by
      have hz : ∀ j, raw3648 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3648step0 = (fun i j => raw3648 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3648step0 raw3648; decide +kernel
      have hl : raw3648step0Labels = raw3648Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3648 raw3648Labels permutation346 hz
    mixedMoment B raw3648step0 raw3648step0Labels = mixedMoment B raw3648step1 raw3648step1Labels := by
      have hz : ∀ j, raw3648step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3648step1 = (fun i j => raw3648step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3648step1 raw3648step0; decide +kernel
      have hl : raw3648step1Labels = raw3648step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3648step0 raw3648step0Labels permutation56 hz
    _ = mixedMoment B node2113 node2113Labels := by rfl

def raw3649 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![0, 2, -2], ![4, -4, 0]]
def raw3649Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3649step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 2, -1], ![0, 2, -2], ![4, -4, 0]]
def raw3649step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3649step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 2, -2], ![4, -4, 0]]
def raw3649step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3649step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -3, 3], ![2, -1, -1], ![2, 0, -2]]
def raw3649step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3649 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3649 raw3649Labels = mixedMoment B node1462 node1462Labels := by
  calc
    mixedMoment B raw3649 raw3649Labels = mixedMoment B raw3649step0 raw3649step0Labels := by
      have hz : ∀ j, raw3649 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3649step0 = (fun i j => raw3649 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3649step0 raw3649; decide +kernel
      have hl : raw3649step0Labels = raw3649Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3649 raw3649Labels permutation346 hz
    mixedMoment B raw3649step0 raw3649step0Labels = mixedMoment B raw3649step1 raw3649step1Labels := by
      have hz : ∀ j, raw3649step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3649step1 = (fun i j => raw3649step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3649step1 raw3649step0; decide +kernel
      have hl : raw3649step1Labels = raw3649step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3649step0 raw3649step0Labels permutation56 hz
    mixedMoment B raw3649step1 raw3649step1Labels = mixedMoment B raw3649step2 raw3649step2Labels := by
      have ha : raw3649step2 = (fun i j => raw3649step1 (permutation26 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3649step2 raw3649step1; decide +kernel
      have hl : raw3649step2Labels = raw3649step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3649step1 raw3649step1Labels permutation26 permutation4
    _ = mixedMoment B node1462 node1462Labels := by rfl

def raw3650 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw3650Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3650step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw3650step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3650 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3650 raw3650Labels = mixedMoment B node2026 node2026Labels := by
  calc
    mixedMoment B raw3650 raw3650Labels = mixedMoment B raw3650step0 raw3650step0Labels := by
      have hz : ∀ j, raw3650 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3650step0 = (fun i j => raw3650 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3650step0 raw3650; decide +kernel
      have hl : raw3650step0Labels = raw3650Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3650 raw3650Labels permutation265 hz
    _ = mixedMoment B node2026 node2026Labels := by rfl

def raw3651 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw3651Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3651step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw3651step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3651step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw3651step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3651 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3651 raw3651Labels = mixedMoment B node2266 node2266Labels := by
  calc
    mixedMoment B raw3651 raw3651Labels = mixedMoment B raw3651step0 raw3651step0Labels := by
      have hz : ∀ j, raw3651 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3651step0 = (fun i j => raw3651 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3651step0 raw3651; decide +kernel
      have hl : raw3651step0Labels = raw3651Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3651 raw3651Labels permutation346 hz
    mixedMoment B raw3651step0 raw3651step0Labels = mixedMoment B raw3651step1 raw3651step1Labels := by
      have hz : ∀ j, raw3651step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3651step1 = (fun i j => raw3651step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3651step1 raw3651step0; decide +kernel
      have hl : raw3651step1Labels = raw3651step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3651step0 raw3651step0Labels permutation56 hz
    _ = mixedMoment B node2266 node2266Labels := by rfl

def raw3652 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![-1, 3, -2], ![3, -3, 0]]
def raw3652Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3652step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![0, 1, -1], ![-1, 3, -2], ![3, -3, 0]]
def raw3652step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3652step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, 1, -1], ![1, -1, 0], ![3, -3, 0]]
def raw3652step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3652 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3652 raw3652Labels = mixedMoment B node2125 node2125Labels := by
  calc
    mixedMoment B raw3652 raw3652Labels = mixedMoment B raw3652step0 raw3652step0Labels := by
      have hz : ∀ j, raw3652 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3652step0 = (fun i j => raw3652 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3652step0 raw3652; decide +kernel
      have hl : raw3652step0Labels = raw3652Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3652 raw3652Labels permutation265 hz
    mixedMoment B raw3652step0 raw3652step0Labels = mixedMoment B raw3652step1 raw3652step1Labels := by
      have ha : raw3652step1 = (fun i j => raw3652step0 (permutation46 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3652step1 raw3652step0; decide +kernel
      have hl : raw3652step1Labels = raw3652step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3652step0 raw3652step0Labels permutation46 permutation2
    _ = mixedMoment B node2125 node2125Labels := by rfl

def raw3653 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![-1, 3, -2], ![4, -4, 0]]
def raw3653Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3653step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![-1, 3, -2], ![4, -4, 0]]
def raw3653step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3653step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 3, -2], ![4, -4, 0]]
def raw3653step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3653step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -3, 3], ![1, 0, -1], ![3, -1, -2]]
def raw3653step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3653 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3653 raw3653Labels = mixedMoment B node1461 node1461Labels := by
  calc
    mixedMoment B raw3653 raw3653Labels = mixedMoment B raw3653step0 raw3653step0Labels := by
      have hz : ∀ j, raw3653 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3653step0 = (fun i j => raw3653 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3653step0 raw3653; decide +kernel
      have hl : raw3653step0Labels = raw3653Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3653 raw3653Labels permutation346 hz
    mixedMoment B raw3653step0 raw3653step0Labels = mixedMoment B raw3653step1 raw3653step1Labels := by
      have hz : ∀ j, raw3653step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3653step1 = (fun i j => raw3653step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3653step1 raw3653step0; decide +kernel
      have hl : raw3653step1Labels = raw3653step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3653step0 raw3653step0Labels permutation56 hz
    mixedMoment B raw3653step1 raw3653step1Labels = mixedMoment B raw3653step2 raw3653step2Labels := by
      have ha : raw3653step2 = (fun i j => raw3653step1 (permutation26 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3653step2 raw3653step1; decide +kernel
      have hl : raw3653step2Labels = raw3653step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3653step1 raw3653step1Labels permutation26 permutation4
    _ = mixedMoment B node1461 node1461Labels := by rfl

def raw3654 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2], ![4, -4, 0]]
def raw3654Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3654step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2], ![4, -4, 0]]
def raw3654step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3654step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -3, 3], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw3654step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3654 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3654 raw3654Labels = mixedMoment B node1458 node1458Labels := by
  calc
    mixedMoment B raw3654 raw3654Labels = mixedMoment B raw3654step0 raw3654step0Labels := by
      have hz : ∀ j, raw3654 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3654step0 = (fun i j => raw3654 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3654step0 raw3654; decide +kernel
      have hl : raw3654step0Labels = raw3654Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3654 raw3654Labels permutation265 hz
    mixedMoment B raw3654step0 raw3654step0Labels = mixedMoment B raw3654step1 raw3654step1Labels := by
      have ha : raw3654step1 = (fun i j => raw3654step0 (permutation128 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3654step1 raw3654step0; decide +kernel
      have hl : raw3654step1Labels = raw3654step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3654step0 raw3654step0Labels permutation128 permutation4
    _ = mixedMoment B node1458 node1458Labels := by rfl

def raw3655 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3655Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3655step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3655step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3655step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw3655step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3655 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3655 raw3655Labels = mixedMoment B node4836 node4836Labels := by
  calc
    mixedMoment B raw3655 raw3655Labels = mixedMoment B raw3655step0 raw3655step0Labels := by
      have hz : ∀ j, raw3655 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3655step0 = (fun i j => raw3655 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3655step0 raw3655; decide +kernel
      have hl : raw3655step0Labels = raw3655Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3655 raw3655Labels permutation346 hz
    mixedMoment B raw3655step0 raw3655step0Labels = mixedMoment B raw3655step1 raw3655step1Labels := by
      have ha : raw3655step1 = (fun i j => raw3655step0 (permutation136 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3655step1 raw3655step0; decide +kernel
      have hl : raw3655step1Labels = raw3655step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3655step0 raw3655step0Labels permutation136 permutation2
    _ = mixedMoment B node4836 node4836Labels := by rfl

def raw3656 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3656Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3656step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3656step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3656step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw3656step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3656 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3656 raw3656Labels = mixedMoment B node4836 node4836Labels := by
  calc
    mixedMoment B raw3656 raw3656Labels = mixedMoment B raw3656step0 raw3656step0Labels := by
      have hz : ∀ j, raw3656 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3656step0 = (fun i j => raw3656 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3656step0 raw3656; decide +kernel
      have hl : raw3656step0Labels = raw3656Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3656 raw3656Labels permutation265 hz
    mixedMoment B raw3656step0 raw3656step0Labels = mixedMoment B raw3656step1 raw3656step1Labels := by
      have ha : raw3656step1 = (fun i j => raw3656step0 (permutation136 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3656step1 raw3656step0; decide +kernel
      have hl : raw3656step1Labels = raw3656step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3656step0 raw3656step0Labels permutation136 permutation2
    _ = mixedMoment B node4836 node4836Labels := by rfl

def raw3657 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3657Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3657step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3657step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3657step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3657step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3657step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-3, 0, 3]]
def raw3657step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3657step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-3, 2, 1]]
def raw3657step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw3657step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![3, -2, -1]]
def raw3657step4Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw3657step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![3, -2, -1]]
def raw3657step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3657 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3657 raw3657Labels = mixedMoment B node4899 node4899Labels := by
  calc
    mixedMoment B raw3657 raw3657Labels = mixedMoment B raw3657step0 raw3657step0Labels := by
      have hz : ∀ j, raw3657 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3657step0 = (fun i j => raw3657 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3657step0 raw3657; decide +kernel
      have hl : raw3657step0Labels = raw3657Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3657 raw3657Labels permutation434 hz
    mixedMoment B raw3657step0 raw3657step0Labels = mixedMoment B raw3657step1 raw3657step1Labels := by
      have hz : ∀ j, raw3657step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3657step1 = (fun i j => raw3657step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3657step1 raw3657step0; decide +kernel
      have hl : raw3657step1Labels = raw3657step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3657step0 raw3657step0Labels permutation80 hz
    mixedMoment B raw3657step1 raw3657step1Labels = mixedMoment B raw3657step2 raw3657step2Labels := by
      have hz : ∀ j, raw3657step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw3657step2 = (fun i j => raw3657step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw3657step2 raw3657step1; decide +kernel
      have hl : raw3657step2Labels = raw3657step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3657step1 raw3657step1Labels permutation14 hz
    mixedMoment B raw3657step2 raw3657step2Labels = mixedMoment B raw3657step3 raw3657step3Labels := by
      have ha : raw3657step3 = (fun i j => raw3657step2 (permutation7 i) (permutation7 j)) := by apply Matrix.ext; unfold raw3657step3 raw3657step2; decide +kernel
      have hl : raw3657step3Labels = raw3657step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3657step2 raw3657step2Labels permutation7 permutation7
    mixedMoment B raw3657step3 raw3657step3Labels = mixedMoment B raw3657step4 raw3657step4Labels := by
      have ha : raw3657step4 = -raw3657step3 := by apply Matrix.ext; change ∀ i j, raw3657step4 i j = -(raw3657step3 i j); unfold raw3657step4 raw3657step3; decide +kernel
      have hl : raw3657step4Labels = raw3657step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3657step4 raw3657step4Labels = mixedMoment B raw3657step5 raw3657step5Labels := by
      have ha : raw3657step5 = raw3657step4 := by apply Matrix.ext; unfold raw3657step5 raw3657step4; decide +kernel
      have hl : raw3657step4Labels = labelEmbedding10 ∘ raw3657step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3657step4 raw3657step4Labels raw3657step5Labels labelEmbedding10 hl
    _ = mixedMoment B node4899 node4899Labels := by rfl

def raw3658 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw3658Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3658step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw3658step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3658step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw3658step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3658step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw3658step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw3658step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw3658step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw3658step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw3658step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3658 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3658 raw3658Labels = mixedMoment B node4890 node4890Labels := by
  calc
    mixedMoment B raw3658 raw3658Labels = mixedMoment B raw3658step0 raw3658step0Labels := by
      have hz : ∀ j, raw3658 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3658step0 = (fun i j => raw3658 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3658step0 raw3658; decide +kernel
      have hl : raw3658step0Labels = raw3658Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3658 raw3658Labels permutation346 hz
    mixedMoment B raw3658step0 raw3658step0Labels = mixedMoment B raw3658step1 raw3658step1Labels := by
      have hz : ∀ j, raw3658step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3658step1 = (fun i j => raw3658step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3658step1 raw3658step0; decide +kernel
      have hl : raw3658step1Labels = raw3658step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3658step0 raw3658step0Labels permutation56 hz
    mixedMoment B raw3658step1 raw3658step1Labels = mixedMoment B raw3658step2 raw3658step2Labels := by
      have ha : raw3658step2 = (fun i j => raw3658step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw3658step2 raw3658step1; decide +kernel
      have hl : raw3658step2Labels = raw3658step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3658step1 raw3658step1Labels permutation29 permutation7
    mixedMoment B raw3658step2 raw3658step2Labels = mixedMoment B raw3658step3 raw3658step3Labels := by
      have ha : raw3658step3 = -raw3658step2 := by apply Matrix.ext; change ∀ i j, raw3658step3 i j = -(raw3658step2 i j); unfold raw3658step3 raw3658step2; decide +kernel
      have hl : raw3658step3Labels = raw3658step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3658step3 raw3658step3Labels = mixedMoment B raw3658step4 raw3658step4Labels := by
      have ha : raw3658step4 = raw3658step3 := by apply Matrix.ext; unfold raw3658step4 raw3658step3; decide +kernel
      have hl : raw3658step3Labels = labelEmbedding10 ∘ raw3658step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3658step3 raw3658step3Labels raw3658step4Labels labelEmbedding10 hl
    _ = mixedMoment B node4890 node4890Labels := by rfl

def raw3659 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![-4, 1, 3]]
def raw3659Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3659step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![-4, 1, 3]]
def raw3659step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3659step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![2, -2, 0], ![-4, 1, 3]]
def raw3659step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3659step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw3659step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3659 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3659 raw3659Labels = mixedMoment B node4500 node4500Labels := by
  calc
    mixedMoment B raw3659 raw3659Labels = mixedMoment B raw3659step0 raw3659step0Labels := by
      have hz : ∀ j, raw3659 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3659step0 = (fun i j => raw3659 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3659step0 raw3659; decide +kernel
      have hl : raw3659step0Labels = raw3659Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3659 raw3659Labels permutation346 hz
    mixedMoment B raw3659step0 raw3659step0Labels = mixedMoment B raw3659step1 raw3659step1Labels := by
      have hz : ∀ j, raw3659step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3659step1 = (fun i j => raw3659step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3659step1 raw3659step0; decide +kernel
      have hl : raw3659step1Labels = raw3659step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3659step0 raw3659step0Labels permutation56 hz
    mixedMoment B raw3659step1 raw3659step1Labels = mixedMoment B raw3659step2 raw3659step2Labels := by
      have ha : raw3659step2 = (fun i j => raw3659step1 (permutation28 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3659step2 raw3659step1; decide +kernel
      have hl : raw3659step2Labels = raw3659step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3659step1 raw3659step1Labels permutation28 permutation2
    _ = mixedMoment B node4500 node4500Labels := by rfl

def raw3660 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3660Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3660step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3660step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3660step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, -3, 3], ![-1, 1, 0], ![-1, 1, 0], ![-2, 2, 0]]
def raw3660step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3660step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw3660step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3660step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw3660step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3660 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3660 raw3660Labels = mixedMoment B node4483 node4483Labels := by
  calc
    mixedMoment B raw3660 raw3660Labels = mixedMoment B raw3660step0 raw3660step0Labels := by
      have hz : ∀ j, raw3660 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3660step0 = (fun i j => raw3660 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3660step0 raw3660; decide +kernel
      have hl : raw3660step0Labels = raw3660Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3660 raw3660Labels permutation346 hz
    mixedMoment B raw3660step0 raw3660step0Labels = mixedMoment B raw3660step1 raw3660step1Labels := by
      have ha : raw3660step1 = (fun i j => raw3660step0 (permutation50 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3660step1 raw3660step0; decide +kernel
      have hl : raw3660step1Labels = raw3660step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3660step0 raw3660step0Labels permutation50 permutation4
    mixedMoment B raw3660step1 raw3660step1Labels = mixedMoment B raw3660step2 raw3660step2Labels := by
      have ha : raw3660step2 = -raw3660step1 := by apply Matrix.ext; change ∀ i j, raw3660step2 i j = -(raw3660step1 i j); unfold raw3660step2 raw3660step1; decide +kernel
      have hl : raw3660step2Labels = raw3660step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3660step2 raw3660step2Labels = mixedMoment B raw3660step3 raw3660step3Labels := by
      have ha : raw3660step3 = raw3660step2 := by apply Matrix.ext; unfold raw3660step3 raw3660step2; decide +kernel
      have hl : raw3660step2Labels = labelEmbedding7 ∘ raw3660step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3660step2 raw3660step2Labels raw3660step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4483 node4483Labels := by rfl

def raw3661 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3661Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3661step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw3661step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3661 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3661 raw3661Labels = mixedMoment B node4822 node4822Labels := by
  calc
    mixedMoment B raw3661 raw3661Labels = mixedMoment B raw3661step0 raw3661step0Labels := by
      have ha : raw3661step0 = (fun i j => raw3661 (permutation623 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3661step0 raw3661; decide +kernel
      have hl : raw3661step0Labels = raw3661Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3661 raw3661Labels permutation623 permutation2
    _ = mixedMoment B node4822 node4822Labels := by rfl

def raw3662 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3662Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3662step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3662step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3662step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3662step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3662step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3662step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw3662step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3662step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3662 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3662 raw3662Labels = mixedMoment B node4892 node4892Labels := by
  calc
    mixedMoment B raw3662 raw3662Labels = mixedMoment B raw3662step0 raw3662step0Labels := by
      have hz : ∀ j, raw3662 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3662step0 = (fun i j => raw3662 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3662step0 raw3662; decide +kernel
      have hl : raw3662step0Labels = raw3662Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3662 raw3662Labels permutation434 hz
    mixedMoment B raw3662step0 raw3662step0Labels = mixedMoment B raw3662step1 raw3662step1Labels := by
      have hz : ∀ j, raw3662step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3662step1 = (fun i j => raw3662step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3662step1 raw3662step0; decide +kernel
      have hl : raw3662step1Labels = raw3662step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3662step0 raw3662step0Labels permutation80 hz
    mixedMoment B raw3662step1 raw3662step1Labels = mixedMoment B raw3662step2 raw3662step2Labels := by
      have ha : raw3662step2 = (fun i j => raw3662step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw3662step2 raw3662step1; decide +kernel
      have hl : raw3662step2Labels = raw3662step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3662step1 raw3662step1Labels permutation8 permutation6
    mixedMoment B raw3662step2 raw3662step2Labels = mixedMoment B raw3662step3 raw3662step3Labels := by
      have ha : raw3662step3 = raw3662step2 := by apply Matrix.ext; unfold raw3662step3 raw3662step2; decide +kernel
      have hl : raw3662step2Labels = labelEmbedding9 ∘ raw3662step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3662step2 raw3662step2Labels raw3662step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4892 node4892Labels := by rfl

def raw3663 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw3663Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3663step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw3663step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3663step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw3663step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw3663step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw3663step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3663 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3663 raw3663Labels = mixedMoment B node4886 node4886Labels := by
  calc
    mixedMoment B raw3663 raw3663Labels = mixedMoment B raw3663step0 raw3663step0Labels := by
      have hz : ∀ j, raw3663 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3663step0 = (fun i j => raw3663 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3663step0 raw3663; decide +kernel
      have hl : raw3663step0Labels = raw3663Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3663 raw3663Labels permutation346 hz
    mixedMoment B raw3663step0 raw3663step0Labels = mixedMoment B raw3663step1 raw3663step1Labels := by
      have ha : raw3663step1 = (fun i j => raw3663step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw3663step1 raw3663step0; decide +kernel
      have hl : raw3663step1Labels = raw3663step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3663step0 raw3663step0Labels permutation32 permutation6
    mixedMoment B raw3663step1 raw3663step1Labels = mixedMoment B raw3663step2 raw3663step2Labels := by
      have ha : raw3663step2 = raw3663step1 := by apply Matrix.ext; unfold raw3663step2 raw3663step1; decide +kernel
      have hl : raw3663step1Labels = labelEmbedding9 ∘ raw3663step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3663step1 raw3663step1Labels raw3663step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4886 node4886Labels := by rfl

def raw3664 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![-4, 1, 3]]
def raw3664Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3664step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0], ![-4, 1, 3]]
def raw3664step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3664step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw3664step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3664 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3664 raw3664Labels = mixedMoment B node4483 node4483Labels := by
  calc
    mixedMoment B raw3664 raw3664Labels = mixedMoment B raw3664step0 raw3664step0Labels := by
      have hz : ∀ j, raw3664 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3664step0 = (fun i j => raw3664 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3664step0 raw3664; decide +kernel
      have hl : raw3664step0Labels = raw3664Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3664 raw3664Labels permutation346 hz
    mixedMoment B raw3664step0 raw3664step0Labels = mixedMoment B raw3664step1 raw3664step1Labels := by
      have ha : raw3664step1 = (fun i j => raw3664step0 (permutation128 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3664step1 raw3664step0; decide +kernel
      have hl : raw3664step1Labels = raw3664step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3664step0 raw3664step0Labels permutation128 permutation2
    _ = mixedMoment B node4483 node4483Labels := by rfl

def raw3665 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3665Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3665step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3665step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3665step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, -3, 3], ![-1, 1, 0], ![-1, 1, 0], ![-2, 2, 0]]
def raw3665step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3665step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw3665step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3665step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw3665step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3665 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3665 raw3665Labels = mixedMoment B node4483 node4483Labels := by
  calc
    mixedMoment B raw3665 raw3665Labels = mixedMoment B raw3665step0 raw3665step0Labels := by
      have hz : ∀ j, raw3665 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3665step0 = (fun i j => raw3665 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3665step0 raw3665; decide +kernel
      have hl : raw3665step0Labels = raw3665Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3665 raw3665Labels permutation265 hz
    mixedMoment B raw3665step0 raw3665step0Labels = mixedMoment B raw3665step1 raw3665step1Labels := by
      have ha : raw3665step1 = (fun i j => raw3665step0 (permutation50 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3665step1 raw3665step0; decide +kernel
      have hl : raw3665step1Labels = raw3665step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3665step0 raw3665step0Labels permutation50 permutation4
    mixedMoment B raw3665step1 raw3665step1Labels = mixedMoment B raw3665step2 raw3665step2Labels := by
      have ha : raw3665step2 = -raw3665step1 := by apply Matrix.ext; change ∀ i j, raw3665step2 i j = -(raw3665step1 i j); unfold raw3665step2 raw3665step1; decide +kernel
      have hl : raw3665step2Labels = raw3665step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3665step2 raw3665step2Labels = mixedMoment B raw3665step3 raw3665step3Labels := by
      have ha : raw3665step3 = raw3665step2 := by apply Matrix.ext; unfold raw3665step3 raw3665step2; decide +kernel
      have hl : raw3665step2Labels = labelEmbedding7 ∘ raw3665step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3665step2 raw3665step2Labels raw3665step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4483 node4483Labels := by rfl

def raw3666 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3666Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3666step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw3666step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3666 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3666 raw3666Labels = mixedMoment B node4822 node4822Labels := by
  calc
    mixedMoment B raw3666 raw3666Labels = mixedMoment B raw3666step0 raw3666step0Labels := by
      have ha : raw3666step0 = (fun i j => raw3666 (permutation602 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3666step0 raw3666; decide +kernel
      have hl : raw3666step0Labels = raw3666Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3666 raw3666Labels permutation602 permutation2
    _ = mixedMoment B node4822 node4822Labels := by rfl

def raw3667 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3667Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3667step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3667step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3667step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3667step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3667step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3667step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw3667step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3667step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3667 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3667 raw3667Labels = mixedMoment B node4892 node4892Labels := by
  calc
    mixedMoment B raw3667 raw3667Labels = mixedMoment B raw3667step0 raw3667step0Labels := by
      have hz : ∀ j, raw3667 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3667step0 = (fun i j => raw3667 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3667step0 raw3667; decide +kernel
      have hl : raw3667step0Labels = raw3667Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3667 raw3667Labels permutation434 hz
    mixedMoment B raw3667step0 raw3667step0Labels = mixedMoment B raw3667step1 raw3667step1Labels := by
      have hz : ∀ j, raw3667step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3667step1 = (fun i j => raw3667step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3667step1 raw3667step0; decide +kernel
      have hl : raw3667step1Labels = raw3667step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3667step0 raw3667step0Labels permutation56 hz
    mixedMoment B raw3667step1 raw3667step1Labels = mixedMoment B raw3667step2 raw3667step2Labels := by
      have ha : raw3667step2 = (fun i j => raw3667step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw3667step2 raw3667step1; decide +kernel
      have hl : raw3667step2Labels = raw3667step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3667step1 raw3667step1Labels permutation8 permutation6
    mixedMoment B raw3667step2 raw3667step2Labels = mixedMoment B raw3667step3 raw3667step3Labels := by
      have ha : raw3667step3 = raw3667step2 := by apply Matrix.ext; unfold raw3667step3 raw3667step2; decide +kernel
      have hl : raw3667step2Labels = labelEmbedding9 ∘ raw3667step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3667step2 raw3667step2Labels raw3667step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4892 node4892Labels := by rfl

def raw3668 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw3668Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3668step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw3668step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3668step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw3668step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw3668step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw3668step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3668 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3668 raw3668Labels = mixedMoment B node4886 node4886Labels := by
  calc
    mixedMoment B raw3668 raw3668Labels = mixedMoment B raw3668step0 raw3668step0Labels := by
      have hz : ∀ j, raw3668 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3668step0 = (fun i j => raw3668 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3668step0 raw3668; decide +kernel
      have hl : raw3668step0Labels = raw3668Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3668 raw3668Labels permutation265 hz
    mixedMoment B raw3668step0 raw3668step0Labels = mixedMoment B raw3668step1 raw3668step1Labels := by
      have ha : raw3668step1 = (fun i j => raw3668step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw3668step1 raw3668step0; decide +kernel
      have hl : raw3668step1Labels = raw3668step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3668step0 raw3668step0Labels permutation32 permutation6
    mixedMoment B raw3668step1 raw3668step1Labels = mixedMoment B raw3668step2 raw3668step2Labels := by
      have ha : raw3668step2 = raw3668step1 := by apply Matrix.ext; unfold raw3668step2 raw3668step1; decide +kernel
      have hl : raw3668step1Labels = labelEmbedding9 ∘ raw3668step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3668step1 raw3668step1Labels raw3668step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4886 node4886Labels := by rfl

def raw3669 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0], ![-4, 1, 3]]
def raw3669Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3669step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0], ![-4, 1, 3]]
def raw3669step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3669step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw3669step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3669 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3669 raw3669Labels = mixedMoment B node4483 node4483Labels := by
  calc
    mixedMoment B raw3669 raw3669Labels = mixedMoment B raw3669step0 raw3669step0Labels := by
      have hz : ∀ j, raw3669 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3669step0 = (fun i j => raw3669 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3669step0 raw3669; decide +kernel
      have hl : raw3669step0Labels = raw3669Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3669 raw3669Labels permutation265 hz
    mixedMoment B raw3669step0 raw3669step0Labels = mixedMoment B raw3669step1 raw3669step1Labels := by
      have ha : raw3669step1 = (fun i j => raw3669step0 (permutation128 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3669step1 raw3669step0; decide +kernel
      have hl : raw3669step1Labels = raw3669step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3669step0 raw3669step0Labels permutation128 permutation2
    _ = mixedMoment B node4483 node4483Labels := by rfl

def raw3670 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3670Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3670step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![0, 0, 0], ![2, -2, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3670step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3670step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -2, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3670step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3670step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, -3, 3], ![-2, 2, 0], ![-2, 2, 0]]
def raw3670step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3670step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 3, -3], ![2, -2, 0], ![2, -2, 0]]
def raw3670step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3670step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 3, -3], ![2, -2, 0], ![2, -2, 0]]
def raw3670step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3670 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3670 raw3670Labels = mixedMoment B node4485 node4485Labels := by
  calc
    mixedMoment B raw3670 raw3670Labels = mixedMoment B raw3670step0 raw3670step0Labels := by
      have hz : ∀ j, raw3670 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3670step0 = (fun i j => raw3670 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3670step0 raw3670; decide +kernel
      have hl : raw3670step0Labels = raw3670Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3670 raw3670Labels permutation346 hz
    mixedMoment B raw3670step0 raw3670step0Labels = mixedMoment B raw3670step1 raw3670step1Labels := by
      have hz : ∀ j, raw3670step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3670step1 = (fun i j => raw3670step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3670step1 raw3670step0; decide +kernel
      have hl : raw3670step1Labels = raw3670step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3670step0 raw3670step0Labels permutation56 hz
    mixedMoment B raw3670step1 raw3670step1Labels = mixedMoment B raw3670step2 raw3670step2Labels := by
      have ha : raw3670step2 = (fun i j => raw3670step1 (permutation12 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3670step2 raw3670step1; decide +kernel
      have hl : raw3670step2Labels = raw3670step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3670step1 raw3670step1Labels permutation12 permutation4
    mixedMoment B raw3670step2 raw3670step2Labels = mixedMoment B raw3670step3 raw3670step3Labels := by
      have ha : raw3670step3 = -raw3670step2 := by apply Matrix.ext; change ∀ i j, raw3670step3 i j = -(raw3670step2 i j); unfold raw3670step3 raw3670step2; decide +kernel
      have hl : raw3670step3Labels = raw3670step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3670step3 raw3670step3Labels = mixedMoment B raw3670step4 raw3670step4Labels := by
      have ha : raw3670step4 = raw3670step3 := by apply Matrix.ext; unfold raw3670step4 raw3670step3; decide +kernel
      have hl : raw3670step3Labels = labelEmbedding7 ∘ raw3670step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3670step3 raw3670step3Labels raw3670step4Labels labelEmbedding7 hl
    _ = mixedMoment B node4485 node4485Labels := by rfl

def raw3671 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3671Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3671step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![2, -2, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3671step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3671step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 3, -3], ![2, -2, 0], ![2, -2, 0]]
def raw3671step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3671 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3671 raw3671Labels = mixedMoment B node4823 node4823Labels := by
  calc
    mixedMoment B raw3671 raw3671Labels = mixedMoment B raw3671step0 raw3671step0Labels := by
      have hz : ∀ j, raw3671 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3671step0 = (fun i j => raw3671 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3671step0 raw3671; decide +kernel
      have hl : raw3671step0Labels = raw3671Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3671 raw3671Labels permutation346 hz
    mixedMoment B raw3671step0 raw3671step0Labels = mixedMoment B raw3671step1 raw3671step1Labels := by
      have ha : raw3671step1 = (fun i j => raw3671step0 (permutation134 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3671step1 raw3671step0; decide +kernel
      have hl : raw3671step1Labels = raw3671step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3671step0 raw3671step0Labels permutation134 permutation2
    _ = mixedMoment B node4823 node4823Labels := by rfl

def raw3672 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3672Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3672step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![2, -2, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3672step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3672step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 3, -3], ![2, -2, 0], ![2, -2, 0]]
def raw3672step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3672 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3672 raw3672Labels = mixedMoment B node4823 node4823Labels := by
  calc
    mixedMoment B raw3672 raw3672Labels = mixedMoment B raw3672step0 raw3672step0Labels := by
      have hz : ∀ j, raw3672 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3672step0 = (fun i j => raw3672 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3672step0 raw3672; decide +kernel
      have hl : raw3672step0Labels = raw3672Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3672 raw3672Labels permutation265 hz
    mixedMoment B raw3672step0 raw3672step0Labels = mixedMoment B raw3672step1 raw3672step1Labels := by
      have ha : raw3672step1 = (fun i j => raw3672step0 (permutation134 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3672step1 raw3672step0; decide +kernel
      have hl : raw3672step1Labels = raw3672step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3672step0 raw3672step0Labels permutation134 permutation2
    _ = mixedMoment B node4823 node4823Labels := by rfl

def raw3673 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw3673Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3673step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw3673step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3673step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw3673step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3673step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3673step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw3673step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3673step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3673 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3673 raw3673Labels = mixedMoment B node4892 node4892Labels := by
  calc
    mixedMoment B raw3673 raw3673Labels = mixedMoment B raw3673step0 raw3673step0Labels := by
      have hz : ∀ j, raw3673 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3673step0 = (fun i j => raw3673 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3673step0 raw3673; decide +kernel
      have hl : raw3673step0Labels = raw3673Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3673 raw3673Labels permutation346 hz
    mixedMoment B raw3673step0 raw3673step0Labels = mixedMoment B raw3673step1 raw3673step1Labels := by
      have hz : ∀ j, raw3673step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3673step1 = (fun i j => raw3673step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3673step1 raw3673step0; decide +kernel
      have hl : raw3673step1Labels = raw3673step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3673step0 raw3673step0Labels permutation56 hz
    mixedMoment B raw3673step1 raw3673step1Labels = mixedMoment B raw3673step2 raw3673step2Labels := by
      have ha : raw3673step2 = (fun i j => raw3673step1 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw3673step2 raw3673step1; decide +kernel
      have hl : raw3673step2Labels = raw3673step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3673step1 raw3673step1Labels permutation10 permutation6
    mixedMoment B raw3673step2 raw3673step2Labels = mixedMoment B raw3673step3 raw3673step3Labels := by
      have ha : raw3673step3 = raw3673step2 := by apply Matrix.ext; unfold raw3673step3 raw3673step2; decide +kernel
      have hl : raw3673step2Labels = labelEmbedding9 ∘ raw3673step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3673step2 raw3673step2Labels raw3673step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4892 node4892Labels := by rfl

def raw3674 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, -2, 0], ![-4, 1, 3]]
def raw3674Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3674step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![2, -2, 0], ![2, -2, 0], ![-4, 1, 3]]
def raw3674step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3674step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![2, -2, 0], ![-4, 1, 3]]
def raw3674step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3674step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 3, -3], ![2, -2, 0], ![2, -2, 0]]
def raw3674step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3674 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3674 raw3674Labels = mixedMoment B node4485 node4485Labels := by
  calc
    mixedMoment B raw3674 raw3674Labels = mixedMoment B raw3674step0 raw3674step0Labels := by
      have hz : ∀ j, raw3674 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3674step0 = (fun i j => raw3674 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3674step0 raw3674; decide +kernel
      have hl : raw3674step0Labels = raw3674Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3674 raw3674Labels permutation346 hz
    mixedMoment B raw3674step0 raw3674step0Labels = mixedMoment B raw3674step1 raw3674step1Labels := by
      have hz : ∀ j, raw3674step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3674step1 = (fun i j => raw3674step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3674step1 raw3674step0; decide +kernel
      have hl : raw3674step1Labels = raw3674step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3674step0 raw3674step0Labels permutation56 hz
    mixedMoment B raw3674step1 raw3674step1Labels = mixedMoment B raw3674step2 raw3674step2Labels := by
      have ha : raw3674step2 = (fun i j => raw3674step1 (permutation26 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3674step2 raw3674step1; decide +kernel
      have hl : raw3674step2Labels = raw3674step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3674step1 raw3674step1Labels permutation26 permutation2
    _ = mixedMoment B node4485 node4485Labels := by rfl

def raw3675 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, -3, 0], ![-3, 0, 3]]
def raw3675Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3675step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![0, 0, 0], ![1, -1, 0], ![3, -3, 0], ![-3, 0, 3]]
def raw3675step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3675step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 4, -3], ![1, -1, 0], ![3, -3, 0], ![-3, 0, 3]]
def raw3675step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3675step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, -3, 3], ![-1, 1, 0], ![-3, 3, 0]]
def raw3675step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3675step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 3, -3], ![1, -1, 0], ![3, -3, 0]]
def raw3675step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3675step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 3, -3], ![1, -1, 0], ![3, -3, 0]]
def raw3675step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3675 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3675 raw3675Labels = mixedMoment B node4484 node4484Labels := by
  calc
    mixedMoment B raw3675 raw3675Labels = mixedMoment B raw3675step0 raw3675step0Labels := by
      have hz : ∀ j, raw3675 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3675step0 = (fun i j => raw3675 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3675step0 raw3675; decide +kernel
      have hl : raw3675step0Labels = raw3675Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3675 raw3675Labels permutation346 hz
    mixedMoment B raw3675step0 raw3675step0Labels = mixedMoment B raw3675step1 raw3675step1Labels := by
      have hz : ∀ j, raw3675step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3675step1 = (fun i j => raw3675step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3675step1 raw3675step0; decide +kernel
      have hl : raw3675step1Labels = raw3675step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3675step0 raw3675step0Labels permutation56 hz
    mixedMoment B raw3675step1 raw3675step1Labels = mixedMoment B raw3675step2 raw3675step2Labels := by
      have ha : raw3675step2 = (fun i j => raw3675step1 (permutation12 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3675step2 raw3675step1; decide +kernel
      have hl : raw3675step2Labels = raw3675step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3675step1 raw3675step1Labels permutation12 permutation4
    mixedMoment B raw3675step2 raw3675step2Labels = mixedMoment B raw3675step3 raw3675step3Labels := by
      have ha : raw3675step3 = -raw3675step2 := by apply Matrix.ext; change ∀ i j, raw3675step3 i j = -(raw3675step2 i j); unfold raw3675step3 raw3675step2; decide +kernel
      have hl : raw3675step3Labels = raw3675step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3675step3 raw3675step3Labels = mixedMoment B raw3675step4 raw3675step4Labels := by
      have ha : raw3675step4 = raw3675step3 := by apply Matrix.ext; unfold raw3675step4 raw3675step3; decide +kernel
      have hl : raw3675step3Labels = labelEmbedding7 ∘ raw3675step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3675step3 raw3675step3Labels raw3675step4Labels labelEmbedding7 hl
    _ = mixedMoment B node4484 node4484Labels := by rfl

def raw3676 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![3, -3, 0], ![-3, 0, 3]]
def raw3676Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3676step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![1, -1, 0], ![3, -3, 0], ![-3, 0, 3]]
def raw3676step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3676step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -3, 3], ![-1, 0, 1], ![-3, 3, 0]]
def raw3676step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3676step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 3, -3], ![1, 0, -1], ![3, -3, 0]]
def raw3676step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3676step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 3, -3], ![1, 0, -1], ![3, -3, 0]]
def raw3676step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3676 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3676 raw3676Labels = mixedMoment B node4751 node4751Labels := by
  calc
    mixedMoment B raw3676 raw3676Labels = mixedMoment B raw3676step0 raw3676step0Labels := by
      have hz : ∀ j, raw3676 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3676step0 = (fun i j => raw3676 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3676step0 raw3676; decide +kernel
      have hl : raw3676step0Labels = raw3676Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3676 raw3676Labels permutation346 hz
    mixedMoment B raw3676step0 raw3676step0Labels = mixedMoment B raw3676step1 raw3676step1Labels := by
      have ha : raw3676step1 = (fun i j => raw3676step0 (permutation116 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3676step1 raw3676step0; decide +kernel
      have hl : raw3676step1Labels = raw3676step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3676step0 raw3676step0Labels permutation116 permutation3
    mixedMoment B raw3676step1 raw3676step1Labels = mixedMoment B raw3676step2 raw3676step2Labels := by
      have ha : raw3676step2 = -raw3676step1 := by apply Matrix.ext; change ∀ i j, raw3676step2 i j = -(raw3676step1 i j); unfold raw3676step2 raw3676step1; decide +kernel
      have hl : raw3676step2Labels = raw3676step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3676step2 raw3676step2Labels = mixedMoment B raw3676step3 raw3676step3Labels := by
      have ha : raw3676step3 = raw3676step2 := by apply Matrix.ext; unfold raw3676step3 raw3676step2; decide +kernel
      have hl : raw3676step2Labels = labelEmbedding6 ∘ raw3676step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3676step2 raw3676step2Labels raw3676step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4751 node4751Labels := by rfl

def raw3677 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -3, 0], ![-3, 0, 3]]
def raw3677Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3677step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![1, -1, 0], ![3, -3, 0], ![-3, 0, 3]]
def raw3677step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3677step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -3, 3], ![-1, 0, 1], ![-3, 3, 0]]
def raw3677step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3677step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 3, -3], ![1, 0, -1], ![3, -3, 0]]
def raw3677step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3677step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 3, -3], ![1, 0, -1], ![3, -3, 0]]
def raw3677step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3677 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3677 raw3677Labels = mixedMoment B node4751 node4751Labels := by
  calc
    mixedMoment B raw3677 raw3677Labels = mixedMoment B raw3677step0 raw3677step0Labels := by
      have hz : ∀ j, raw3677 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3677step0 = (fun i j => raw3677 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3677step0 raw3677; decide +kernel
      have hl : raw3677step0Labels = raw3677Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3677 raw3677Labels permutation265 hz
    mixedMoment B raw3677step0 raw3677step0Labels = mixedMoment B raw3677step1 raw3677step1Labels := by
      have ha : raw3677step1 = (fun i j => raw3677step0 (permutation116 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3677step1 raw3677step0; decide +kernel
      have hl : raw3677step1Labels = raw3677step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3677step0 raw3677step0Labels permutation116 permutation3
    mixedMoment B raw3677step1 raw3677step1Labels = mixedMoment B raw3677step2 raw3677step2Labels := by
      have ha : raw3677step2 = -raw3677step1 := by apply Matrix.ext; change ∀ i j, raw3677step2 i j = -(raw3677step1 i j); unfold raw3677step2 raw3677step1; decide +kernel
      have hl : raw3677step2Labels = raw3677step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3677step2 raw3677step2Labels = mixedMoment B raw3677step3 raw3677step3Labels := by
      have ha : raw3677step3 = raw3677step2 := by apply Matrix.ext; unfold raw3677step3 raw3677step2; decide +kernel
      have hl : raw3677step2Labels = labelEmbedding6 ∘ raw3677step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3677step2 raw3677step2Labels raw3677step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4751 node4751Labels := by rfl

def raw3678 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![-3, 0, 3]]
def raw3678Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3678step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![-3, 0, 3]]
def raw3678step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3678step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![3, -3, 0], ![-3, 0, 3]]
def raw3678step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3678step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, 3, -3], ![3, -3, 0], ![-3, 0, 3]]
def raw3678step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3678step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![3, -3, 0]]
def raw3678step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3678 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3678 raw3678Labels = mixedMoment B node4900 node4900Labels := by
  calc
    mixedMoment B raw3678 raw3678Labels = mixedMoment B raw3678step0 raw3678step0Labels := by
      have hz : ∀ j, raw3678 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3678step0 = (fun i j => raw3678 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3678step0 raw3678; decide +kernel
      have hl : raw3678step0Labels = raw3678Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3678 raw3678Labels permutation434 hz
    mixedMoment B raw3678step0 raw3678step0Labels = mixedMoment B raw3678step1 raw3678step1Labels := by
      have hz : ∀ j, raw3678step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3678step1 = (fun i j => raw3678step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3678step1 raw3678step0; decide +kernel
      have hl : raw3678step1Labels = raw3678step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3678step0 raw3678step0Labels permutation80 hz
    mixedMoment B raw3678step1 raw3678step1Labels = mixedMoment B raw3678step2 raw3678step2Labels := by
      have hz : ∀ j, raw3678step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw3678step2 = (fun i j => raw3678step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw3678step2 raw3678step1; decide +kernel
      have hl : raw3678step2Labels = raw3678step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3678step1 raw3678step1Labels permutation14 hz
    mixedMoment B raw3678step2 raw3678step2Labels = mixedMoment B raw3678step3 raw3678step3Labels := by
      have ha : raw3678step3 = (fun i j => raw3678step2 (permutation6 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3678step3 raw3678step2; decide +kernel
      have hl : raw3678step3Labels = raw3678step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3678step2 raw3678step2Labels permutation6 permutation2
    _ = mixedMoment B node4900 node4900Labels := by rfl

def raw3679 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, -3, 0], ![-4, 1, 3]]
def raw3679Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3679step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![3, -3, 0], ![-4, 1, 3]]
def raw3679step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3679step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![3, -3, 0], ![-4, 1, 3]]
def raw3679step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3679step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 3, -3], ![1, -1, 0], ![3, -3, 0]]
def raw3679step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3679 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3679 raw3679Labels = mixedMoment B node4484 node4484Labels := by
  calc
    mixedMoment B raw3679 raw3679Labels = mixedMoment B raw3679step0 raw3679step0Labels := by
      have hz : ∀ j, raw3679 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3679step0 = (fun i j => raw3679 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3679step0 raw3679; decide +kernel
      have hl : raw3679step0Labels = raw3679Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3679 raw3679Labels permutation346 hz
    mixedMoment B raw3679step0 raw3679step0Labels = mixedMoment B raw3679step1 raw3679step1Labels := by
      have hz : ∀ j, raw3679step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3679step1 = (fun i j => raw3679step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3679step1 raw3679step0; decide +kernel
      have hl : raw3679step1Labels = raw3679step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3679step0 raw3679step0Labels permutation56 hz
    mixedMoment B raw3679step1 raw3679step1Labels = mixedMoment B raw3679step2 raw3679step2Labels := by
      have ha : raw3679step2 = (fun i j => raw3679step1 (permutation26 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3679step2 raw3679step1; decide +kernel
      have hl : raw3679step2Labels = raw3679step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3679step1 raw3679step1Labels permutation26 permutation2
    _ = mixedMoment B node4484 node4484Labels := by rfl

def raw3680 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw3680Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3680step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw3680step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3680step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 4, -3], ![1, -1, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw3680step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3680step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![-1, 1, 0], ![-1, -2, 3], ![-2, 2, 0]]
def raw3680step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3680step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw3680step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3680step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw3680step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3680 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3680 raw3680Labels = mixedMoment B node4500 node4500Labels := by
  calc
    mixedMoment B raw3680 raw3680Labels = mixedMoment B raw3680step0 raw3680step0Labels := by
      have hz : ∀ j, raw3680 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3680step0 = (fun i j => raw3680 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3680step0 raw3680; decide +kernel
      have hl : raw3680step0Labels = raw3680Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3680 raw3680Labels permutation346 hz
    mixedMoment B raw3680step0 raw3680step0Labels = mixedMoment B raw3680step1 raw3680step1Labels := by
      have hz : ∀ j, raw3680step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3680step1 = (fun i j => raw3680step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3680step1 raw3680step0; decide +kernel
      have hl : raw3680step1Labels = raw3680step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3680step0 raw3680step0Labels permutation56 hz
    mixedMoment B raw3680step1 raw3680step1Labels = mixedMoment B raw3680step2 raw3680step2Labels := by
      have ha : raw3680step2 = (fun i j => raw3680step1 (permutation9 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3680step2 raw3680step1; decide +kernel
      have hl : raw3680step2Labels = raw3680step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3680step1 raw3680step1Labels permutation9 permutation4
    mixedMoment B raw3680step2 raw3680step2Labels = mixedMoment B raw3680step3 raw3680step3Labels := by
      have ha : raw3680step3 = -raw3680step2 := by apply Matrix.ext; change ∀ i j, raw3680step3 i j = -(raw3680step2 i j); unfold raw3680step3 raw3680step2; decide +kernel
      have hl : raw3680step3Labels = raw3680step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3680step3 raw3680step3Labels = mixedMoment B raw3680step4 raw3680step4Labels := by
      have ha : raw3680step4 = raw3680step3 := by apply Matrix.ext; unfold raw3680step4 raw3680step3; decide +kernel
      have hl : raw3680step3Labels = labelEmbedding7 ∘ raw3680step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3680step3 raw3680step3Labels raw3680step4Labels labelEmbedding7 hl
    _ = mixedMoment B node4500 node4500Labels := by rfl

def raw3681 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw3681Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3681step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw3681step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3681step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, -2, 3], ![-2, 2, 0]]
def raw3681step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3681step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw3681step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3681step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw3681step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3681 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3681 raw3681Labels = mixedMoment B node4836 node4836Labels := by
  calc
    mixedMoment B raw3681 raw3681Labels = mixedMoment B raw3681step0 raw3681step0Labels := by
      have hz : ∀ j, raw3681 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3681step0 = (fun i j => raw3681 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3681step0 raw3681; decide +kernel
      have hl : raw3681step0Labels = raw3681Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3681 raw3681Labels permutation346 hz
    mixedMoment B raw3681step0 raw3681step0Labels = mixedMoment B raw3681step1 raw3681step1Labels := by
      have ha : raw3681step1 = (fun i j => raw3681step0 (permutation33 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3681step1 raw3681step0; decide +kernel
      have hl : raw3681step1Labels = raw3681step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3681step0 raw3681step0Labels permutation33 permutation4
    mixedMoment B raw3681step1 raw3681step1Labels = mixedMoment B raw3681step2 raw3681step2Labels := by
      have ha : raw3681step2 = -raw3681step1 := by apply Matrix.ext; change ∀ i j, raw3681step2 i j = -(raw3681step1 i j); unfold raw3681step2 raw3681step1; decide +kernel
      have hl : raw3681step2Labels = raw3681step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3681step2 raw3681step2Labels = mixedMoment B raw3681step3 raw3681step3Labels := by
      have ha : raw3681step3 = raw3681step2 := by apply Matrix.ext; unfold raw3681step3 raw3681step2; decide +kernel
      have hl : raw3681step2Labels = labelEmbedding7 ∘ raw3681step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3681step2 raw3681step2Labels raw3681step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4836 node4836Labels := by rfl

def raw3682 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw3682Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3682step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw3682step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3682step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, -2, 3], ![-2, 2, 0]]
def raw3682step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3682step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw3682step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3682step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw3682step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3682 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3682 raw3682Labels = mixedMoment B node4836 node4836Labels := by
  calc
    mixedMoment B raw3682 raw3682Labels = mixedMoment B raw3682step0 raw3682step0Labels := by
      have hz : ∀ j, raw3682 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3682step0 = (fun i j => raw3682 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3682step0 raw3682; decide +kernel
      have hl : raw3682step0Labels = raw3682Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3682 raw3682Labels permutation265 hz
    mixedMoment B raw3682step0 raw3682step0Labels = mixedMoment B raw3682step1 raw3682step1Labels := by
      have ha : raw3682step1 = (fun i j => raw3682step0 (permutation33 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3682step1 raw3682step0; decide +kernel
      have hl : raw3682step1Labels = raw3682step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3682step0 raw3682step0Labels permutation33 permutation4
    mixedMoment B raw3682step1 raw3682step1Labels = mixedMoment B raw3682step2 raw3682step2Labels := by
      have ha : raw3682step2 = -raw3682step1 := by apply Matrix.ext; change ∀ i j, raw3682step2 i j = -(raw3682step1 i j); unfold raw3682step2 raw3682step1; decide +kernel
      have hl : raw3682step2Labels = raw3682step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3682step2 raw3682step2Labels = mixedMoment B raw3682step3 raw3682step3Labels := by
      have ha : raw3682step3 = raw3682step2 := by apply Matrix.ext; unfold raw3682step3 raw3682step2; decide +kernel
      have hl : raw3682step2Labels = labelEmbedding7 ∘ raw3682step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3682step2 raw3682step2Labels raw3682step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4836 node4836Labels := by rfl

def raw3683 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw3683Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3683step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw3683step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3683step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw3683step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3683step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![-2, -1, 3]]
def raw3683step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3683step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![3, -2, -1]]
def raw3683step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw3683step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![3, -2, -1]]
def raw3683step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3683 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3683 raw3683Labels = mixedMoment B node4899 node4899Labels := by
  calc
    mixedMoment B raw3683 raw3683Labels = mixedMoment B raw3683step0 raw3683step0Labels := by
      have hz : ∀ j, raw3683 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3683step0 = (fun i j => raw3683 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3683step0 raw3683; decide +kernel
      have hl : raw3683step0Labels = raw3683Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3683 raw3683Labels permutation434 hz
    mixedMoment B raw3683step0 raw3683step0Labels = mixedMoment B raw3683step1 raw3683step1Labels := by
      have hz : ∀ j, raw3683step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3683step1 = (fun i j => raw3683step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3683step1 raw3683step0; decide +kernel
      have hl : raw3683step1Labels = raw3683step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3683step0 raw3683step0Labels permutation80 hz
    mixedMoment B raw3683step1 raw3683step1Labels = mixedMoment B raw3683step2 raw3683step2Labels := by
      have hz : ∀ j, raw3683step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw3683step2 = (fun i j => raw3683step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw3683step2 raw3683step1; decide +kernel
      have hl : raw3683step2Labels = raw3683step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3683step1 raw3683step1Labels permutation14 hz
    mixedMoment B raw3683step2 raw3683step2Labels = mixedMoment B raw3683step3 raw3683step3Labels := by
      have ha : raw3683step3 = (fun i j => raw3683step2 (permutation2 i) (permutation6 j)) := by apply Matrix.ext; unfold raw3683step3 raw3683step2; decide +kernel
      have hl : raw3683step3Labels = raw3683step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3683step2 raw3683step2Labels permutation2 permutation6
    mixedMoment B raw3683step3 raw3683step3Labels = mixedMoment B raw3683step4 raw3683step4Labels := by
      have ha : raw3683step4 = raw3683step3 := by apply Matrix.ext; unfold raw3683step4 raw3683step3; decide +kernel
      have hl : raw3683step3Labels = labelEmbedding9 ∘ raw3683step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3683step3 raw3683step3Labels raw3683step4Labels labelEmbedding9 hl
    _ = mixedMoment B node4899 node4899Labels := by rfl

def raw3684 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw3684Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3684step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw3684step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3684step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw3684step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3684step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw3684step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw3684step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw3684step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3684 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3684 raw3684Labels = mixedMoment B node4890 node4890Labels := by
  calc
    mixedMoment B raw3684 raw3684Labels = mixedMoment B raw3684step0 raw3684step0Labels := by
      have hz : ∀ j, raw3684 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3684step0 = (fun i j => raw3684 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3684step0 raw3684; decide +kernel
      have hl : raw3684step0Labels = raw3684Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3684 raw3684Labels permutation346 hz
    mixedMoment B raw3684step0 raw3684step0Labels = mixedMoment B raw3684step1 raw3684step1Labels := by
      have hz : ∀ j, raw3684step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3684step1 = (fun i j => raw3684step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3684step1 raw3684step0; decide +kernel
      have hl : raw3684step1Labels = raw3684step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3684step0 raw3684step0Labels permutation56 hz
    mixedMoment B raw3684step1 raw3684step1Labels = mixedMoment B raw3684step2 raw3684step2Labels := by
      have ha : raw3684step2 = (fun i j => raw3684step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw3684step2 raw3684step1; decide +kernel
      have hl : raw3684step2Labels = raw3684step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3684step1 raw3684step1Labels permutation8 permutation6
    mixedMoment B raw3684step2 raw3684step2Labels = mixedMoment B raw3684step3 raw3684step3Labels := by
      have ha : raw3684step3 = raw3684step2 := by apply Matrix.ext; unfold raw3684step3 raw3684step2; decide +kernel
      have hl : raw3684step2Labels = labelEmbedding9 ∘ raw3684step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3684step2 raw3684step2Labels raw3684step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4890 node4890Labels := by rfl

def raw3685 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3685Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3685step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3685step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3685step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3685step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3685 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3685 raw3685Labels = mixedMoment B node2716 node2716Labels := by
  calc
    mixedMoment B raw3685 raw3685Labels = mixedMoment B raw3685step0 raw3685step0Labels := by
      have hz : ∀ j, raw3685 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3685step0 = (fun i j => raw3685 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3685step0 raw3685; decide +kernel
      have hl : raw3685step0Labels = raw3685Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3685 raw3685Labels permutation346 hz
    mixedMoment B raw3685step0 raw3685step0Labels = mixedMoment B raw3685step1 raw3685step1Labels := by
      have ha : raw3685step1 = (fun i j => raw3685step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw3685step1 raw3685step0; decide +kernel
      have hl : raw3685step1Labels = raw3685step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3685step0 raw3685step0Labels permutation32 permutation6
    _ = mixedMoment B node2716 node2716Labels := by rfl

def raw3686 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3686Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3686step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3686step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3686step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3686step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3686 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3686 raw3686Labels = mixedMoment B node2716 node2716Labels := by
  calc
    mixedMoment B raw3686 raw3686Labels = mixedMoment B raw3686step0 raw3686step0Labels := by
      have hz : ∀ j, raw3686 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3686step0 = (fun i j => raw3686 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3686step0 raw3686; decide +kernel
      have hl : raw3686step0Labels = raw3686Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3686 raw3686Labels permutation265 hz
    mixedMoment B raw3686step0 raw3686step0Labels = mixedMoment B raw3686step1 raw3686step1Labels := by
      have ha : raw3686step1 = (fun i j => raw3686step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw3686step1 raw3686step0; decide +kernel
      have hl : raw3686step1Labels = raw3686step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3686step0 raw3686step0Labels permutation32 permutation6
    _ = mixedMoment B node2716 node2716Labels := by rfl

def raw3687 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3687Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3687step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3687step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3687step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3687step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3687step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-3, 0, 3]]
def raw3687step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3687step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![3, -3, 0]]
def raw3687step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3687 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3687 raw3687Labels = mixedMoment B node2778 node2778Labels := by
  calc
    mixedMoment B raw3687 raw3687Labels = mixedMoment B raw3687step0 raw3687step0Labels := by
      have hz : ∀ j, raw3687 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3687step0 = (fun i j => raw3687 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3687step0 raw3687; decide +kernel
      have hl : raw3687step0Labels = raw3687Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3687 raw3687Labels permutation434 hz
    mixedMoment B raw3687step0 raw3687step0Labels = mixedMoment B raw3687step1 raw3687step1Labels := by
      have hz : ∀ j, raw3687step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3687step1 = (fun i j => raw3687step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3687step1 raw3687step0; decide +kernel
      have hl : raw3687step1Labels = raw3687step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3687step0 raw3687step0Labels permutation80 hz
    mixedMoment B raw3687step1 raw3687step1Labels = mixedMoment B raw3687step2 raw3687step2Labels := by
      have hz : ∀ j, raw3687step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw3687step2 = (fun i j => raw3687step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw3687step2 raw3687step1; decide +kernel
      have hl : raw3687step2Labels = raw3687step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3687step1 raw3687step1Labels permutation14 hz
    mixedMoment B raw3687step2 raw3687step2Labels = mixedMoment B raw3687step3 raw3687step3Labels := by
      have ha : raw3687step3 = (fun i j => raw3687step2 (permutation2 i) (permutation6 j)) := by apply Matrix.ext; unfold raw3687step3 raw3687step2; decide +kernel
      have hl : raw3687step3Labels = raw3687step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3687step2 raw3687step2Labels permutation2 permutation6
    _ = mixedMoment B node2778 node2778Labels := by rfl

def raw3688 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw3688Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3688step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw3688step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3688step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw3688step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3688step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw3688step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3688 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3688 raw3688Labels = mixedMoment B node2755 node2755Labels := by
  calc
    mixedMoment B raw3688 raw3688Labels = mixedMoment B raw3688step0 raw3688step0Labels := by
      have hz : ∀ j, raw3688 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3688step0 = (fun i j => raw3688 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3688step0 raw3688; decide +kernel
      have hl : raw3688step0Labels = raw3688Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3688 raw3688Labels permutation346 hz
    mixedMoment B raw3688step0 raw3688step0Labels = mixedMoment B raw3688step1 raw3688step1Labels := by
      have hz : ∀ j, raw3688step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3688step1 = (fun i j => raw3688step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3688step1 raw3688step0; decide +kernel
      have hl : raw3688step1Labels = raw3688step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3688step0 raw3688step0Labels permutation56 hz
    mixedMoment B raw3688step1 raw3688step1Labels = mixedMoment B raw3688step2 raw3688step2Labels := by
      have ha : raw3688step2 = (fun i j => raw3688step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw3688step2 raw3688step1; decide +kernel
      have hl : raw3688step2Labels = raw3688step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3688step1 raw3688step1Labels permutation8 permutation6
    _ = mixedMoment B node2755 node2755Labels := by rfl

def raw3689 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![-4, 1, 3]]
def raw3689Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3689step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![-4, 1, 3]]
def raw3689step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3689step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![2, -2, 0], ![-4, 1, 3]]
def raw3689step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3689step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw3689step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3689 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3689 raw3689Labels = mixedMoment B node1436 node1436Labels := by
  calc
    mixedMoment B raw3689 raw3689Labels = mixedMoment B raw3689step0 raw3689step0Labels := by
      have hz : ∀ j, raw3689 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3689step0 = (fun i j => raw3689 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3689step0 raw3689; decide +kernel
      have hl : raw3689step0Labels = raw3689Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3689 raw3689Labels permutation346 hz
    mixedMoment B raw3689step0 raw3689step0Labels = mixedMoment B raw3689step1 raw3689step1Labels := by
      have hz : ∀ j, raw3689step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3689step1 = (fun i j => raw3689step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3689step1 raw3689step0; decide +kernel
      have hl : raw3689step1Labels = raw3689step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3689step0 raw3689step0Labels permutation56 hz
    mixedMoment B raw3689step1 raw3689step1Labels = mixedMoment B raw3689step2 raw3689step2Labels := by
      have ha : raw3689step2 = (fun i j => raw3689step1 (permutation26 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3689step2 raw3689step1; decide +kernel
      have hl : raw3689step2Labels = raw3689step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3689step1 raw3689step1Labels permutation26 permutation3
    _ = mixedMoment B node1436 node1436Labels := by rfl

def raw3690 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3690Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3690step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3690step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3690step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3690step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3690 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3690 raw3690Labels = mixedMoment B node1702 node1702Labels := by
  calc
    mixedMoment B raw3690 raw3690Labels = mixedMoment B raw3690step0 raw3690step0Labels := by
      have hz : ∀ j, raw3690 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3690step0 = (fun i j => raw3690 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3690step0 raw3690; decide +kernel
      have hl : raw3690step0Labels = raw3690Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3690 raw3690Labels permutation346 hz
    mixedMoment B raw3690step0 raw3690step0Labels = mixedMoment B raw3690step1 raw3690step1Labels := by
      have ha : raw3690step1 = (fun i j => raw3690step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw3690step1 raw3690step0; decide +kernel
      have hl : raw3690step1Labels = raw3690step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3690step0 raw3690step0Labels permutation32 permutation6
    _ = mixedMoment B node1702 node1702Labels := by rfl

def raw3691 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3691Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3691step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3691step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3691 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3691 raw3691Labels = mixedMoment B node2188 node2188Labels := by
  calc
    mixedMoment B raw3691 raw3691Labels = mixedMoment B raw3691step0 raw3691step0Labels := by
      have ha : raw3691step0 = (fun i j => raw3691 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw3691step0 raw3691; decide +kernel
      have hl : raw3691step0Labels = raw3691Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3691 raw3691Labels permutation176 permutation6
    _ = mixedMoment B node2188 node2188Labels := by rfl

def raw3692 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3692Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3692step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3692step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3692step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3692step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3692step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3692step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3692 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3692 raw3692Labels = mixedMoment B node2255 node2255Labels := by
  calc
    mixedMoment B raw3692 raw3692Labels = mixedMoment B raw3692step0 raw3692step0Labels := by
      have hz : ∀ j, raw3692 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3692step0 = (fun i j => raw3692 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3692step0 raw3692; decide +kernel
      have hl : raw3692step0Labels = raw3692Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3692 raw3692Labels permutation434 hz
    mixedMoment B raw3692step0 raw3692step0Labels = mixedMoment B raw3692step1 raw3692step1Labels := by
      have hz : ∀ j, raw3692step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3692step1 = (fun i j => raw3692step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3692step1 raw3692step0; decide +kernel
      have hl : raw3692step1Labels = raw3692step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3692step0 raw3692step0Labels permutation80 hz
    mixedMoment B raw3692step1 raw3692step1Labels = mixedMoment B raw3692step2 raw3692step2Labels := by
      have ha : raw3692step2 = (fun i j => raw3692step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw3692step2 raw3692step1; decide +kernel
      have hl : raw3692step2Labels = raw3692step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3692step1 raw3692step1Labels permutation8 permutation6
    _ = mixedMoment B node2255 node2255Labels := by rfl

def raw3693 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw3693Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3693step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw3693step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3693step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw3693step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3693 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3693 raw3693Labels = mixedMoment B node2235 node2235Labels := by
  calc
    mixedMoment B raw3693 raw3693Labels = mixedMoment B raw3693step0 raw3693step0Labels := by
      have hz : ∀ j, raw3693 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3693step0 = (fun i j => raw3693 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3693step0 raw3693; decide +kernel
      have hl : raw3693step0Labels = raw3693Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3693 raw3693Labels permutation346 hz
    mixedMoment B raw3693step0 raw3693step0Labels = mixedMoment B raw3693step1 raw3693step1Labels := by
      have ha : raw3693step1 = (fun i j => raw3693step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw3693step1 raw3693step0; decide +kernel
      have hl : raw3693step1Labels = raw3693step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3693step0 raw3693step0Labels permutation32 permutation6
    _ = mixedMoment B node2235 node2235Labels := by rfl

def raw3694 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![-4, 1, 3]]
def raw3694Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3694step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0], ![-4, 1, 3]]
def raw3694step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3694step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -3, 3], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw3694step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3694 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3694 raw3694Labels = mixedMoment B node1351 node1351Labels := by
  calc
    mixedMoment B raw3694 raw3694Labels = mixedMoment B raw3694step0 raw3694step0Labels := by
      have hz : ∀ j, raw3694 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3694step0 = (fun i j => raw3694 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3694step0 raw3694; decide +kernel
      have hl : raw3694step0Labels = raw3694Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3694 raw3694Labels permutation346 hz
    mixedMoment B raw3694step0 raw3694step0Labels = mixedMoment B raw3694step1 raw3694step1Labels := by
      have ha : raw3694step1 = (fun i j => raw3694step0 (permutation128 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3694step1 raw3694step0; decide +kernel
      have hl : raw3694step1Labels = raw3694step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3694step0 raw3694step0Labels permutation128 permutation3
    _ = mixedMoment B node1351 node1351Labels := by rfl

def raw3695 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3695Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3695step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3695step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3695step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3695step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3695 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3695 raw3695Labels = mixedMoment B node1702 node1702Labels := by
  calc
    mixedMoment B raw3695 raw3695Labels = mixedMoment B raw3695step0 raw3695step0Labels := by
      have hz : ∀ j, raw3695 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3695step0 = (fun i j => raw3695 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3695step0 raw3695; decide +kernel
      have hl : raw3695step0Labels = raw3695Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3695 raw3695Labels permutation265 hz
    mixedMoment B raw3695step0 raw3695step0Labels = mixedMoment B raw3695step1 raw3695step1Labels := by
      have ha : raw3695step1 = (fun i j => raw3695step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw3695step1 raw3695step0; decide +kernel
      have hl : raw3695step1Labels = raw3695step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3695step0 raw3695step0Labels permutation32 permutation6
    _ = mixedMoment B node1702 node1702Labels := by rfl

def raw3696 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3696Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3696step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3696step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3696 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3696 raw3696Labels = mixedMoment B node2188 node2188Labels := by
  calc
    mixedMoment B raw3696 raw3696Labels = mixedMoment B raw3696step0 raw3696step0Labels := by
      have ha : raw3696step0 = (fun i j => raw3696 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw3696step0 raw3696; decide +kernel
      have hl : raw3696step0Labels = raw3696Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3696 raw3696Labels permutation152 permutation6
    _ = mixedMoment B node2188 node2188Labels := by rfl

def raw3697 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3697Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3697step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3697step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3697step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3697step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3697step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3697step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3697 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3697 raw3697Labels = mixedMoment B node2255 node2255Labels := by
  calc
    mixedMoment B raw3697 raw3697Labels = mixedMoment B raw3697step0 raw3697step0Labels := by
      have hz : ∀ j, raw3697 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3697step0 = (fun i j => raw3697 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3697step0 raw3697; decide +kernel
      have hl : raw3697step0Labels = raw3697Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3697 raw3697Labels permutation434 hz
    mixedMoment B raw3697step0 raw3697step0Labels = mixedMoment B raw3697step1 raw3697step1Labels := by
      have hz : ∀ j, raw3697step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3697step1 = (fun i j => raw3697step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3697step1 raw3697step0; decide +kernel
      have hl : raw3697step1Labels = raw3697step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3697step0 raw3697step0Labels permutation56 hz
    mixedMoment B raw3697step1 raw3697step1Labels = mixedMoment B raw3697step2 raw3697step2Labels := by
      have ha : raw3697step2 = (fun i j => raw3697step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw3697step2 raw3697step1; decide +kernel
      have hl : raw3697step2Labels = raw3697step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3697step1 raw3697step1Labels permutation8 permutation6
    _ = mixedMoment B node2255 node2255Labels := by rfl

def raw3698 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw3698Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3698step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw3698step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3698step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw3698step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3698 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3698 raw3698Labels = mixedMoment B node2235 node2235Labels := by
  calc
    mixedMoment B raw3698 raw3698Labels = mixedMoment B raw3698step0 raw3698step0Labels := by
      have hz : ∀ j, raw3698 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3698step0 = (fun i j => raw3698 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3698step0 raw3698; decide +kernel
      have hl : raw3698step0Labels = raw3698Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3698 raw3698Labels permutation265 hz
    mixedMoment B raw3698step0 raw3698step0Labels = mixedMoment B raw3698step1 raw3698step1Labels := by
      have ha : raw3698step1 = (fun i j => raw3698step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw3698step1 raw3698step0; decide +kernel
      have hl : raw3698step1Labels = raw3698step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3698step0 raw3698step0Labels permutation32 permutation6
    _ = mixedMoment B node2235 node2235Labels := by rfl

def raw3699 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0], ![-4, 1, 3]]
def raw3699Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3699step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0], ![-4, 1, 3]]
def raw3699step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3699step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -3, 3], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw3699step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3699 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3699 raw3699Labels = mixedMoment B node1351 node1351Labels := by
  calc
    mixedMoment B raw3699 raw3699Labels = mixedMoment B raw3699step0 raw3699step0Labels := by
      have hz : ∀ j, raw3699 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3699step0 = (fun i j => raw3699 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3699step0 raw3699; decide +kernel
      have hl : raw3699step0Labels = raw3699Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3699 raw3699Labels permutation265 hz
    mixedMoment B raw3699step0 raw3699step0Labels = mixedMoment B raw3699step1 raw3699step1Labels := by
      have ha : raw3699step1 = (fun i j => raw3699step0 (permutation128 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3699step1 raw3699step0; decide +kernel
      have hl : raw3699step1Labels = raw3699step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3699step0 raw3699step0Labels permutation128 permutation3
    _ = mixedMoment B node1351 node1351Labels := by rfl

def raw3700 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3700Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3700step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![0, 0, 0], ![2, -2, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3700step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3700step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -2, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3700step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3700step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 2, -2], ![3, -3, 0]]
def raw3700step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3700 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3700 raw3700Labels = mixedMoment B node1733 node1733Labels := by
  calc
    mixedMoment B raw3700 raw3700Labels = mixedMoment B raw3700step0 raw3700step0Labels := by
      have hz : ∀ j, raw3700 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3700step0 = (fun i j => raw3700 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3700step0 raw3700; decide +kernel
      have hl : raw3700step0Labels = raw3700Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3700 raw3700Labels permutation346 hz
    mixedMoment B raw3700step0 raw3700step0Labels = mixedMoment B raw3700step1 raw3700step1Labels := by
      have hz : ∀ j, raw3700step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3700step1 = (fun i j => raw3700step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3700step1 raw3700step0; decide +kernel
      have hl : raw3700step1Labels = raw3700step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3700step0 raw3700step0Labels permutation56 hz
    mixedMoment B raw3700step1 raw3700step1Labels = mixedMoment B raw3700step2 raw3700step2Labels := by
      have ha : raw3700step2 = (fun i j => raw3700step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw3700step2 raw3700step1; decide +kernel
      have hl : raw3700step2Labels = raw3700step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3700step1 raw3700step1Labels permutation8 permutation6
    _ = mixedMoment B node1733 node1733Labels := by rfl

def raw3701 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3701Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3701step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![2, -2, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3701step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3701step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![0, 2, -2], ![3, -3, 0]]
def raw3701step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3701 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3701 raw3701Labels = mixedMoment B node2210 node2210Labels := by
  calc
    mixedMoment B raw3701 raw3701Labels = mixedMoment B raw3701step0 raw3701step0Labels := by
      have hz : ∀ j, raw3701 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3701step0 = (fun i j => raw3701 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3701step0 raw3701; decide +kernel
      have hl : raw3701step0Labels = raw3701Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3701 raw3701Labels permutation346 hz
    mixedMoment B raw3701step0 raw3701step0Labels = mixedMoment B raw3701step1 raw3701step1Labels := by
      have ha : raw3701step1 = (fun i j => raw3701step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw3701step1 raw3701step0; decide +kernel
      have hl : raw3701step1Labels = raw3701step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3701step0 raw3701step0Labels permutation32 permutation6
    _ = mixedMoment B node2210 node2210Labels := by rfl

def raw3702 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3702Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3702step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![2, -2, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3702step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3702step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![0, 2, -2], ![3, -3, 0]]
def raw3702step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3702 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3702 raw3702Labels = mixedMoment B node2210 node2210Labels := by
  calc
    mixedMoment B raw3702 raw3702Labels = mixedMoment B raw3702step0 raw3702step0Labels := by
      have hz : ∀ j, raw3702 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3702step0 = (fun i j => raw3702 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3702step0 raw3702; decide +kernel
      have hl : raw3702step0Labels = raw3702Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3702 raw3702Labels permutation265 hz
    mixedMoment B raw3702step0 raw3702step0Labels = mixedMoment B raw3702step1 raw3702step1Labels := by
      have ha : raw3702step1 = (fun i j => raw3702step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw3702step1 raw3702step0; decide +kernel
      have hl : raw3702step1Labels = raw3702step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3702step0 raw3702step0Labels permutation32 permutation6
    _ = mixedMoment B node2210 node2210Labels := by rfl

def raw3703 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw3703Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3703step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw3703step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3703step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw3703step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3703step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3703step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3703 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3703 raw3703Labels = mixedMoment B node2255 node2255Labels := by
  calc
    mixedMoment B raw3703 raw3703Labels = mixedMoment B raw3703step0 raw3703step0Labels := by
      have hz : ∀ j, raw3703 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3703step0 = (fun i j => raw3703 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3703step0 raw3703; decide +kernel
      have hl : raw3703step0Labels = raw3703Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3703 raw3703Labels permutation346 hz
    mixedMoment B raw3703step0 raw3703step0Labels = mixedMoment B raw3703step1 raw3703step1Labels := by
      have hz : ∀ j, raw3703step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3703step1 = (fun i j => raw3703step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3703step1 raw3703step0; decide +kernel
      have hl : raw3703step1Labels = raw3703step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3703step0 raw3703step0Labels permutation56 hz
    mixedMoment B raw3703step1 raw3703step1Labels = mixedMoment B raw3703step2 raw3703step2Labels := by
      have ha : raw3703step2 = (fun i j => raw3703step1 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw3703step2 raw3703step1; decide +kernel
      have hl : raw3703step2Labels = raw3703step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3703step1 raw3703step1Labels permutation10 permutation6
    _ = mixedMoment B node2255 node2255Labels := by rfl

def raw3704 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, -2, 0], ![-4, 1, 3]]
def raw3704Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3704step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![2, -2, 0], ![2, -2, 0], ![-4, 1, 3]]
def raw3704step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3704step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![2, -2, 0], ![-4, 1, 3]]
def raw3704step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3704step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -3, 3], ![2, 0, -2], ![2, 0, -2]]
def raw3704step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3704 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3704 raw3704Labels = mixedMoment B node1353 node1353Labels := by
  calc
    mixedMoment B raw3704 raw3704Labels = mixedMoment B raw3704step0 raw3704step0Labels := by
      have hz : ∀ j, raw3704 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3704step0 = (fun i j => raw3704 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3704step0 raw3704; decide +kernel
      have hl : raw3704step0Labels = raw3704Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3704 raw3704Labels permutation346 hz
    mixedMoment B raw3704step0 raw3704step0Labels = mixedMoment B raw3704step1 raw3704step1Labels := by
      have hz : ∀ j, raw3704step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3704step1 = (fun i j => raw3704step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3704step1 raw3704step0; decide +kernel
      have hl : raw3704step1Labels = raw3704step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3704step0 raw3704step0Labels permutation56 hz
    mixedMoment B raw3704step1 raw3704step1Labels = mixedMoment B raw3704step2 raw3704step2Labels := by
      have ha : raw3704step2 = (fun i j => raw3704step1 (permutation26 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3704step2 raw3704step1; decide +kernel
      have hl : raw3704step2Labels = raw3704step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3704step1 raw3704step1Labels permutation26 permutation3
    _ = mixedMoment B node1353 node1353Labels := by rfl

def raw3705 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, -3, 0], ![-3, 0, 3]]
def raw3705Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3705step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![0, 0, 0], ![1, -1, 0], ![3, -3, 0], ![-3, 0, 3]]
def raw3705step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3705step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 4, -3], ![1, -1, 0], ![3, -3, 0], ![-3, 0, 3]]
def raw3705step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3705step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 3, -3], ![3, -3, 0]]
def raw3705step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3705 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3705 raw3705Labels = mixedMoment B node1719 node1719Labels := by
  calc
    mixedMoment B raw3705 raw3705Labels = mixedMoment B raw3705step0 raw3705step0Labels := by
      have hz : ∀ j, raw3705 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3705step0 = (fun i j => raw3705 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3705step0 raw3705; decide +kernel
      have hl : raw3705step0Labels = raw3705Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3705 raw3705Labels permutation346 hz
    mixedMoment B raw3705step0 raw3705step0Labels = mixedMoment B raw3705step1 raw3705step1Labels := by
      have hz : ∀ j, raw3705step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3705step1 = (fun i j => raw3705step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3705step1 raw3705step0; decide +kernel
      have hl : raw3705step1Labels = raw3705step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3705step0 raw3705step0Labels permutation56 hz
    mixedMoment B raw3705step1 raw3705step1Labels = mixedMoment B raw3705step2 raw3705step2Labels := by
      have ha : raw3705step2 = (fun i j => raw3705step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw3705step2 raw3705step1; decide +kernel
      have hl : raw3705step2Labels = raw3705step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3705step1 raw3705step1Labels permutation8 permutation6
    _ = mixedMoment B node1719 node1719Labels := by rfl

def raw3706 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![3, -3, 0], ![-3, 0, 3]]
def raw3706Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3706step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![1, -1, 0], ![3, -3, 0], ![-3, 0, 3]]
def raw3706step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3706step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -3, 3], ![-1, 0, 1], ![-3, 3, 0]]
def raw3706step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3706step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 3, -3], ![1, 0, -1], ![3, -3, 0]]
def raw3706step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3706 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3706 raw3706Labels = mixedMoment B node1933 node1933Labels := by
  calc
    mixedMoment B raw3706 raw3706Labels = mixedMoment B raw3706step0 raw3706step0Labels := by
      have hz : ∀ j, raw3706 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3706step0 = (fun i j => raw3706 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3706step0 raw3706; decide +kernel
      have hl : raw3706step0Labels = raw3706Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3706 raw3706Labels permutation346 hz
    mixedMoment B raw3706step0 raw3706step0Labels = mixedMoment B raw3706step1 raw3706step1Labels := by
      have ha : raw3706step1 = (fun i j => raw3706step0 (permutation116 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3706step1 raw3706step0; decide +kernel
      have hl : raw3706step1Labels = raw3706step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3706step0 raw3706step0Labels permutation116 permutation3
    mixedMoment B raw3706step1 raw3706step1Labels = mixedMoment B raw3706step2 raw3706step2Labels := by
      have ha : raw3706step2 = -raw3706step1 := by apply Matrix.ext; change ∀ i j, raw3706step2 i j = -(raw3706step1 i j); unfold raw3706step2 raw3706step1; decide +kernel
      have hl : raw3706step2Labels = raw3706step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1933 node1933Labels := by rfl

def raw3707 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -3, 0], ![-3, 0, 3]]
def raw3707Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3707step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![1, -1, 0], ![3, -3, 0], ![-3, 0, 3]]
def raw3707step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3707step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -3, 3], ![-1, 0, 1], ![-3, 3, 0]]
def raw3707step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3707step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 3, -3], ![1, 0, -1], ![3, -3, 0]]
def raw3707step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3707 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3707 raw3707Labels = mixedMoment B node1933 node1933Labels := by
  calc
    mixedMoment B raw3707 raw3707Labels = mixedMoment B raw3707step0 raw3707step0Labels := by
      have hz : ∀ j, raw3707 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3707step0 = (fun i j => raw3707 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3707step0 raw3707; decide +kernel
      have hl : raw3707step0Labels = raw3707Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3707 raw3707Labels permutation265 hz
    mixedMoment B raw3707step0 raw3707step0Labels = mixedMoment B raw3707step1 raw3707step1Labels := by
      have ha : raw3707step1 = (fun i j => raw3707step0 (permutation116 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3707step1 raw3707step0; decide +kernel
      have hl : raw3707step1Labels = raw3707step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3707step0 raw3707step0Labels permutation116 permutation3
    mixedMoment B raw3707step1 raw3707step1Labels = mixedMoment B raw3707step2 raw3707step2Labels := by
      have ha : raw3707step2 = -raw3707step1 := by apply Matrix.ext; change ∀ i j, raw3707step2 i j = -(raw3707step1 i j); unfold raw3707step2 raw3707step1; decide +kernel
      have hl : raw3707step2Labels = raw3707step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1933 node1933Labels := by rfl

def raw3708 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![-3, 0, 3]]
def raw3708Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3708step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![-3, 0, 3]]
def raw3708step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3708step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![3, -3, 0], ![-3, 0, 3]]
def raw3708step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3708step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, 3, -3], ![3, -3, 0], ![-3, 0, 3]]
def raw3708step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3708step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![0, -3, 3], ![-3, 3, 0]]
def raw3708step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3708step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![3, -3, 0]]
def raw3708step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3708 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3708 raw3708Labels = mixedMoment B node2285 node2285Labels := by
  calc
    mixedMoment B raw3708 raw3708Labels = mixedMoment B raw3708step0 raw3708step0Labels := by
      have hz : ∀ j, raw3708 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3708step0 = (fun i j => raw3708 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3708step0 raw3708; decide +kernel
      have hl : raw3708step0Labels = raw3708Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3708 raw3708Labels permutation434 hz
    mixedMoment B raw3708step0 raw3708step0Labels = mixedMoment B raw3708step1 raw3708step1Labels := by
      have hz : ∀ j, raw3708step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3708step1 = (fun i j => raw3708step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3708step1 raw3708step0; decide +kernel
      have hl : raw3708step1Labels = raw3708step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3708step0 raw3708step0Labels permutation80 hz
    mixedMoment B raw3708step1 raw3708step1Labels = mixedMoment B raw3708step2 raw3708step2Labels := by
      have hz : ∀ j, raw3708step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw3708step2 = (fun i j => raw3708step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw3708step2 raw3708step1; decide +kernel
      have hl : raw3708step2Labels = raw3708step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3708step1 raw3708step1Labels permutation14 hz
    mixedMoment B raw3708step2 raw3708step2Labels = mixedMoment B raw3708step3 raw3708step3Labels := by
      have ha : raw3708step3 = (fun i j => raw3708step2 (permutation4 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3708step3 raw3708step2; decide +kernel
      have hl : raw3708step3Labels = raw3708step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3708step2 raw3708step2Labels permutation4 permutation3
    mixedMoment B raw3708step3 raw3708step3Labels = mixedMoment B raw3708step4 raw3708step4Labels := by
      have ha : raw3708step4 = -raw3708step3 := by apply Matrix.ext; change ∀ i j, raw3708step4 i j = -(raw3708step3 i j); unfold raw3708step4 raw3708step3; decide +kernel
      have hl : raw3708step4Labels = raw3708step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2285 node2285Labels := by rfl

def raw3709 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, -3, 0], ![-4, 1, 3]]
def raw3709Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3709step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![3, -3, 0], ![-4, 1, 3]]
def raw3709step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3709step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![3, -3, 0], ![-4, 1, 3]]
def raw3709step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3709step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -3, 3], ![1, 0, -1], ![3, 0, -3]]
def raw3709step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3709 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3709 raw3709Labels = mixedMoment B node1352 node1352Labels := by
  calc
    mixedMoment B raw3709 raw3709Labels = mixedMoment B raw3709step0 raw3709step0Labels := by
      have hz : ∀ j, raw3709 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3709step0 = (fun i j => raw3709 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3709step0 raw3709; decide +kernel
      have hl : raw3709step0Labels = raw3709Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3709 raw3709Labels permutation346 hz
    mixedMoment B raw3709step0 raw3709step0Labels = mixedMoment B raw3709step1 raw3709step1Labels := by
      have hz : ∀ j, raw3709step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3709step1 = (fun i j => raw3709step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3709step1 raw3709step0; decide +kernel
      have hl : raw3709step1Labels = raw3709step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3709step0 raw3709step0Labels permutation56 hz
    mixedMoment B raw3709step1 raw3709step1Labels = mixedMoment B raw3709step2 raw3709step2Labels := by
      have ha : raw3709step2 = (fun i j => raw3709step1 (permutation26 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3709step2 raw3709step1; decide +kernel
      have hl : raw3709step2Labels = raw3709step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3709step1 raw3709step1Labels permutation26 permutation3
    _ = mixedMoment B node1352 node1352Labels := by rfl

def raw3710 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw3710Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3710step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw3710step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3710step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 4, -3], ![1, -1, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw3710step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3710step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw3710step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3710 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3710 raw3710Labels = mixedMoment B node1716 node1716Labels := by
  calc
    mixedMoment B raw3710 raw3710Labels = mixedMoment B raw3710step0 raw3710step0Labels := by
      have hz : ∀ j, raw3710 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3710step0 = (fun i j => raw3710 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3710step0 raw3710; decide +kernel
      have hl : raw3710step0Labels = raw3710Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3710 raw3710Labels permutation346 hz
    mixedMoment B raw3710step0 raw3710step0Labels = mixedMoment B raw3710step1 raw3710step1Labels := by
      have hz : ∀ j, raw3710step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3710step1 = (fun i j => raw3710step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3710step1 raw3710step0; decide +kernel
      have hl : raw3710step1Labels = raw3710step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3710step0 raw3710step0Labels permutation56 hz
    mixedMoment B raw3710step1 raw3710step1Labels = mixedMoment B raw3710step2 raw3710step2Labels := by
      have ha : raw3710step2 = (fun i j => raw3710step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw3710step2 raw3710step1; decide +kernel
      have hl : raw3710step2Labels = raw3710step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3710step1 raw3710step1Labels permutation8 permutation6
    _ = mixedMoment B node1716 node1716Labels := by rfl

def raw3711 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw3711Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3711step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw3711step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3711step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw3711step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3711 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3711 raw3711Labels = mixedMoment B node2197 node2197Labels := by
  calc
    mixedMoment B raw3711 raw3711Labels = mixedMoment B raw3711step0 raw3711step0Labels := by
      have hz : ∀ j, raw3711 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3711step0 = (fun i j => raw3711 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3711step0 raw3711; decide +kernel
      have hl : raw3711step0Labels = raw3711Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3711 raw3711Labels permutation346 hz
    mixedMoment B raw3711step0 raw3711step0Labels = mixedMoment B raw3711step1 raw3711step1Labels := by
      have ha : raw3711step1 = (fun i j => raw3711step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw3711step1 raw3711step0; decide +kernel
      have hl : raw3711step1Labels = raw3711step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3711step0 raw3711step0Labels permutation32 permutation6
    _ = mixedMoment B node2197 node2197Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
