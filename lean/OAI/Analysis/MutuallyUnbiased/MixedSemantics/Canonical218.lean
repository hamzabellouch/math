import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes10
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes11
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes14
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes29
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes30
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes36
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes37
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes51
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes65
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes67
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes73
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes74
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes78
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw27904 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw27904Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27904step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw27904step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27904step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw27904step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27904 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27904 raw27904Labels = mixedMoment B node913 node913Labels := by
  calc
    mixedMoment B raw27904 raw27904Labels = mixedMoment B raw27904step0 raw27904step0Labels := by
      have hz : ∀ j, raw27904 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27904step0 = (fun i j => raw27904 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27904step0 raw27904; decide +kernel
      have hl : raw27904step0Labels = raw27904Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27904 raw27904Labels permutation346 hz
    mixedMoment B raw27904step0 raw27904step0Labels = mixedMoment B raw27904step1 raw27904step1Labels := by
      have ha : raw27904step1 = (fun i j => raw27904step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27904step1 raw27904step0; decide +kernel
      have hl : raw27904step1Labels = raw27904step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27904step0 raw27904step0Labels permutation32 permutation3
    _ = mixedMoment B node913 node913Labels := by rfl

def raw27905 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw27905Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27905step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw27905step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27905step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw27905step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27905 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27905 raw27905Labels = mixedMoment B node2326 node2326Labels := by
  calc
    mixedMoment B raw27905 raw27905Labels = mixedMoment B raw27905step0 raw27905step0Labels := by
      have hz : ∀ j, raw27905 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27905step0 = (fun i j => raw27905 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27905step0 raw27905; decide +kernel
      have hl : raw27905step0Labels = raw27905Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27905 raw27905Labels permutation346 hz
    mixedMoment B raw27905step0 raw27905step0Labels = mixedMoment B raw27905step1 raw27905step1Labels := by
      have ha : raw27905step1 = (fun i j => raw27905step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27905step1 raw27905step0; decide +kernel
      have hl : raw27905step1Labels = raw27905step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27905step0 raw27905step0Labels permutation32 permutation3
    _ = mixedMoment B node2326 node2326Labels := by rfl

def raw27906 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw27906Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27906step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw27906step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27906 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27906 raw27906Labels = mixedMoment B node2422 node2422Labels := by
  calc
    mixedMoment B raw27906 raw27906Labels = mixedMoment B raw27906step0 raw27906step0Labels := by
      have ha : raw27906step0 = (fun i j => raw27906 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27906step0 raw27906; decide +kernel
      have hl : raw27906step0Labels = raw27906Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27906 raw27906Labels permutation176 permutation3
    _ = mixedMoment B node2422 node2422Labels := by rfl

def raw27907 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![2, -1, -1], ![3, -1, -2]]
def raw27907Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27907step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![2, -1, -1], ![3, -1, -2]]
def raw27907step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27907step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw27907step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27907 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27907 raw27907Labels = mixedMoment B node2531 node2531Labels := by
  calc
    mixedMoment B raw27907 raw27907Labels = mixedMoment B raw27907step0 raw27907step0Labels := by
      have hz : ∀ j, raw27907 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27907step0 = (fun i j => raw27907 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27907step0 raw27907; decide +kernel
      have hl : raw27907step0Labels = raw27907Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27907 raw27907Labels permutation346 hz
    mixedMoment B raw27907step0 raw27907step0Labels = mixedMoment B raw27907step1 raw27907step1Labels := by
      have ha : raw27907step1 = (fun i j => raw27907step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27907step1 raw27907step0; decide +kernel
      have hl : raw27907step1Labels = raw27907step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27907step0 raw27907step0Labels permutation32 permutation3
    _ = mixedMoment B node2531 node2531Labels := by rfl

def raw27908 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw27908Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27908step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw27908step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27908step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw27908step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27908 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27908 raw27908Labels = mixedMoment B node2576 node2576Labels := by
  calc
    mixedMoment B raw27908 raw27908Labels = mixedMoment B raw27908step0 raw27908step0Labels := by
      have hz : ∀ j, raw27908 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27908step0 = (fun i j => raw27908 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27908step0 raw27908; decide +kernel
      have hl : raw27908step0Labels = raw27908Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27908 raw27908Labels permutation346 hz
    mixedMoment B raw27908step0 raw27908step0Labels = mixedMoment B raw27908step1 raw27908step1Labels := by
      have ha : raw27908step1 = (fun i j => raw27908step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27908step1 raw27908step0; decide +kernel
      have hl : raw27908step1Labels = raw27908step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27908step0 raw27908step0Labels permutation33 permutation3
    _ = mixedMoment B node2576 node2576Labels := by rfl

def raw27909 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![4, -2, -2]]
def raw27909Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27909step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![4, -2, -2]]
def raw27909step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27909step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![4, -2, -2]]
def raw27909step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27909 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27909 raw27909Labels = mixedMoment B node908 node908Labels := by
  calc
    mixedMoment B raw27909 raw27909Labels = mixedMoment B raw27909step0 raw27909step0Labels := by
      have hz : ∀ j, raw27909 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27909step0 = (fun i j => raw27909 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27909step0 raw27909; decide +kernel
      have hl : raw27909step0Labels = raw27909Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27909 raw27909Labels permutation346 hz
    mixedMoment B raw27909step0 raw27909step0Labels = mixedMoment B raw27909step1 raw27909step1Labels := by
      have ha : raw27909step1 = (fun i j => raw27909step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27909step1 raw27909step0; decide +kernel
      have hl : raw27909step1Labels = raw27909step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27909step0 raw27909step0Labels permutation32 permutation3
    _ = mixedMoment B node908 node908Labels := by rfl

def raw27910 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![4, -2, -2]]
def raw27910Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27910step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![4, -2, -2]]
def raw27910step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27910step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![1, -1, 0], ![0, 1, -1], ![-2, 1, 1], ![-3, 1, 2]]
def raw27910step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27910step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw27910step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27910 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27910 raw27910Labels = mixedMoment B node1154 node1154Labels := by
  calc
    mixedMoment B raw27910 raw27910Labels = mixedMoment B raw27910step0 raw27910step0Labels := by
      have hz : ∀ j, raw27910 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27910step0 = (fun i j => raw27910 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27910step0 raw27910; decide +kernel
      have hl : raw27910step0Labels = raw27910Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27910 raw27910Labels permutation346 hz
    mixedMoment B raw27910step0 raw27910step0Labels = mixedMoment B raw27910step1 raw27910step1Labels := by
      have ha : raw27910step1 = (fun i j => raw27910step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27910step1 raw27910step0; decide +kernel
      have hl : raw27910step1Labels = raw27910step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27910step0 raw27910step0Labels permutation151 permutation3
    mixedMoment B raw27910step1 raw27910step1Labels = mixedMoment B raw27910step2 raw27910step2Labels := by
      have ha : raw27910step2 = -raw27910step1 := by apply Matrix.ext; change ∀ i j, raw27910step2 i j = -(raw27910step1 i j); unfold raw27910step2 raw27910step1; decide +kernel
      have hl : raw27910step2Labels = raw27910step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1154 node1154Labels := by rfl

def raw27911 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![4, -2, -2]]
def raw27911Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27911step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -2, -2], ![1, -1, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw27911step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27911step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw27911step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27911 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27911 raw27911Labels = mixedMoment B node1148 node1148Labels := by
  calc
    mixedMoment B raw27911 raw27911Labels = mixedMoment B raw27911step0 raw27911step0Labels := by
      have ha : raw27911step0 = (fun i j => raw27911 (permutation686 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27911step0 raw27911; decide +kernel
      have hl : raw27911step0Labels = raw27911Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27911 raw27911Labels permutation686 permutation3
    mixedMoment B raw27911step0 raw27911step0Labels = mixedMoment B raw27911step1 raw27911step1Labels := by
      have ha : raw27911step1 = -raw27911step0 := by apply Matrix.ext; change ∀ i j, raw27911step1 i j = -(raw27911step0 i j); unfold raw27911step1 raw27911step0; decide +kernel
      have hl : raw27911step1Labels = raw27911step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1148 node1148Labels := by rfl

def raw27912 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw27912Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27912step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw27912step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27912step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-3, 1, 2]]
def raw27912step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27912step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw27912step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27912 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27912 raw27912Labels = mixedMoment B node1163 node1163Labels := by
  calc
    mixedMoment B raw27912 raw27912Labels = mixedMoment B raw27912step0 raw27912step0Labels := by
      have hz : ∀ j, raw27912 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27912step0 = (fun i j => raw27912 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27912step0 raw27912; decide +kernel
      have hl : raw27912step0Labels = raw27912Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27912 raw27912Labels permutation346 hz
    mixedMoment B raw27912step0 raw27912step0Labels = mixedMoment B raw27912step1 raw27912step1Labels := by
      have ha : raw27912step1 = (fun i j => raw27912step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27912step1 raw27912step0; decide +kernel
      have hl : raw27912step1Labels = raw27912step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27912step0 raw27912step0Labels permutation149 permutation3
    mixedMoment B raw27912step1 raw27912step1Labels = mixedMoment B raw27912step2 raw27912step2Labels := by
      have ha : raw27912step2 = -raw27912step1 := by apply Matrix.ext; change ∀ i j, raw27912step2 i j = -(raw27912step1 i j); unfold raw27912step2 raw27912step1; decide +kernel
      have hl : raw27912step2Labels = raw27912step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1163 node1163Labels := by rfl

def raw27913 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![4, -2, -2]]
def raw27913Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27913step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![4, -2, -2]]
def raw27913step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27913step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw27913step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27913step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw27913step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27913 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27913 raw27913Labels = mixedMoment B node1215 node1215Labels := by
  calc
    mixedMoment B raw27913 raw27913Labels = mixedMoment B raw27913step0 raw27913step0Labels := by
      have hz : ∀ j, raw27913 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27913step0 = (fun i j => raw27913 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27913step0 raw27913; decide +kernel
      have hl : raw27913step0Labels = raw27913Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27913 raw27913Labels permutation346 hz
    mixedMoment B raw27913step0 raw27913step0Labels = mixedMoment B raw27913step1 raw27913step1Labels := by
      have ha : raw27913step1 = (fun i j => raw27913step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27913step1 raw27913step0; decide +kernel
      have hl : raw27913step1Labels = raw27913step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27913step0 raw27913step0Labels permutation145 permutation3
    mixedMoment B raw27913step1 raw27913step1Labels = mixedMoment B raw27913step2 raw27913step2Labels := by
      have ha : raw27913step2 = -raw27913step1 := by apply Matrix.ext; change ∀ i j, raw27913step2 i j = -(raw27913step1 i j); unfold raw27913step2 raw27913step1; decide +kernel
      have hl : raw27913step2Labels = raw27913step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1215 node1215Labels := by rfl

def raw27914 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw27914Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27914step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw27914step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27914step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw27914step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27914step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw27914step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27914 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27914 raw27914Labels = mixedMoment B node3482 node3482Labels := by
  calc
    mixedMoment B raw27914 raw27914Labels = mixedMoment B raw27914step0 raw27914step0Labels := by
      have hz : ∀ j, raw27914 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27914step0 = (fun i j => raw27914 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27914step0 raw27914; decide +kernel
      have hl : raw27914step0Labels = raw27914Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27914 raw27914Labels permutation346 hz
    mixedMoment B raw27914step0 raw27914step0Labels = mixedMoment B raw27914step1 raw27914step1Labels := by
      have ha : raw27914step1 = (fun i j => raw27914step0 (permutation150 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27914step1 raw27914step0; decide +kernel
      have hl : raw27914step1Labels = raw27914step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27914step0 raw27914step0Labels permutation150 permutation7
    mixedMoment B raw27914step1 raw27914step1Labels = mixedMoment B raw27914step2 raw27914step2Labels := by
      have ha : raw27914step2 = raw27914step1 := by apply Matrix.ext; unfold raw27914step2 raw27914step1; decide +kernel
      have hl : raw27914step1Labels = labelEmbedding1 ∘ raw27914step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27914step1 raw27914step1Labels raw27914step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3482 node3482Labels := by rfl

def raw27915 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw27915Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27915step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw27915step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27915step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw27915step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27915 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27915 raw27915Labels = mixedMoment B node3467 node3467Labels := by
  calc
    mixedMoment B raw27915 raw27915Labels = mixedMoment B raw27915step0 raw27915step0Labels := by
      have ha : raw27915step0 = (fun i j => raw27915 (permutation682 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27915step0 raw27915; decide +kernel
      have hl : raw27915step0Labels = raw27915Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27915 raw27915Labels permutation682 permutation7
    mixedMoment B raw27915step0 raw27915step0Labels = mixedMoment B raw27915step1 raw27915step1Labels := by
      have ha : raw27915step1 = raw27915step0 := by apply Matrix.ext; unfold raw27915step1 raw27915step0; decide +kernel
      have hl : raw27915step0Labels = labelEmbedding1 ∘ raw27915step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27915step0 raw27915step0Labels raw27915step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3467 node3467Labels := by rfl

def raw27916 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw27916Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27916step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw27916step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27916step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw27916step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27916step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw27916step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27916 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27916 raw27916Labels = mixedMoment B node3483 node3483Labels := by
  calc
    mixedMoment B raw27916 raw27916Labels = mixedMoment B raw27916step0 raw27916step0Labels := by
      have hz : ∀ j, raw27916 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27916step0 = (fun i j => raw27916 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27916step0 raw27916; decide +kernel
      have hl : raw27916step0Labels = raw27916Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27916 raw27916Labels permutation346 hz
    mixedMoment B raw27916step0 raw27916step0Labels = mixedMoment B raw27916step1 raw27916step1Labels := by
      have ha : raw27916step1 = (fun i j => raw27916step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27916step1 raw27916step0; decide +kernel
      have hl : raw27916step1Labels = raw27916step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27916step0 raw27916step0Labels permutation149 permutation7
    mixedMoment B raw27916step1 raw27916step1Labels = mixedMoment B raw27916step2 raw27916step2Labels := by
      have ha : raw27916step2 = raw27916step1 := by apply Matrix.ext; unfold raw27916step2 raw27916step1; decide +kernel
      have hl : raw27916step1Labels = labelEmbedding1 ∘ raw27916step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27916step1 raw27916step1Labels raw27916step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3483 node3483Labels := by rfl

def raw27917 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw27917Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27917step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw27917step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27917step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw27917step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27917step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw27917step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27917 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27917 raw27917Labels = mixedMoment B node3544 node3544Labels := by
  calc
    mixedMoment B raw27917 raw27917Labels = mixedMoment B raw27917step0 raw27917step0Labels := by
      have hz : ∀ j, raw27917 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27917step0 = (fun i j => raw27917 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27917step0 raw27917; decide +kernel
      have hl : raw27917step0Labels = raw27917Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27917 raw27917Labels permutation346 hz
    mixedMoment B raw27917step0 raw27917step0Labels = mixedMoment B raw27917step1 raw27917step1Labels := by
      have ha : raw27917step1 = (fun i j => raw27917step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27917step1 raw27917step0; decide +kernel
      have hl : raw27917step1Labels = raw27917step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27917step0 raw27917step0Labels permutation151 permutation7
    mixedMoment B raw27917step1 raw27917step1Labels = mixedMoment B raw27917step2 raw27917step2Labels := by
      have ha : raw27917step2 = raw27917step1 := by apply Matrix.ext; unfold raw27917step2 raw27917step1; decide +kernel
      have hl : raw27917step1Labels = labelEmbedding1 ∘ raw27917step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27917step1 raw27917step1Labels raw27917step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3544 node3544Labels := by rfl

def raw27918 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw27918Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27918step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw27918step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27918step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw27918step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27918step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw27918step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27918 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27918 raw27918Labels = mixedMoment B node3816 node3816Labels := by
  calc
    mixedMoment B raw27918 raw27918Labels = mixedMoment B raw27918step0 raw27918step0Labels := by
      have hz : ∀ j, raw27918 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27918step0 = (fun i j => raw27918 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27918step0 raw27918; decide +kernel
      have hl : raw27918step0Labels = raw27918Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27918 raw27918Labels permutation346 hz
    mixedMoment B raw27918step0 raw27918step0Labels = mixedMoment B raw27918step1 raw27918step1Labels := by
      have ha : raw27918step1 = (fun i j => raw27918step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27918step1 raw27918step0; decide +kernel
      have hl : raw27918step1Labels = raw27918step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27918step0 raw27918step0Labels permutation151 permutation7
    mixedMoment B raw27918step1 raw27918step1Labels = mixedMoment B raw27918step2 raw27918step2Labels := by
      have ha : raw27918step2 = raw27918step1 := by apply Matrix.ext; unfold raw27918step2 raw27918step1; decide +kernel
      have hl : raw27918step1Labels = labelEmbedding1 ∘ raw27918step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27918step1 raw27918step1Labels raw27918step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3816 node3816Labels := by rfl

def raw27919 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw27919Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27919step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw27919step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27919step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw27919step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27919step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw27919step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27919step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw27919step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27919 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27919 raw27919Labels = mixedMoment B node1723 node1723Labels := by
  calc
    mixedMoment B raw27919 raw27919Labels = mixedMoment B raw27919step0 raw27919step0Labels := by
      have hz : ∀ j, raw27919 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27919step0 = (fun i j => raw27919 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27919step0 raw27919; decide +kernel
      have hl : raw27919step0Labels = raw27919Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27919 raw27919Labels permutation346 hz
    mixedMoment B raw27919step0 raw27919step0Labels = mixedMoment B raw27919step1 raw27919step1Labels := by
      have ha : raw27919step1 = (fun i j => raw27919step0 (permutation44 i) (permutation5 j)) := by apply Matrix.ext; unfold raw27919step1 raw27919step0; decide +kernel
      have hl : raw27919step1Labels = raw27919step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27919step0 raw27919step0Labels permutation44 permutation5
    mixedMoment B raw27919step1 raw27919step1Labels = mixedMoment B raw27919step2 raw27919step2Labels := by
      have ha : raw27919step2 = -raw27919step1 := by apply Matrix.ext; change ∀ i j, raw27919step2 i j = -(raw27919step1 i j); unfold raw27919step2 raw27919step1; decide +kernel
      have hl : raw27919step2Labels = raw27919step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27919step2 raw27919step2Labels = mixedMoment B raw27919step3 raw27919step3Labels := by
      have ha : raw27919step3 = raw27919step2 := by apply Matrix.ext; unfold raw27919step3 raw27919step2; decide +kernel
      have hl : raw27919step2Labels = labelEmbedding1 ∘ raw27919step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27919step2 raw27919step2Labels raw27919step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1723 node1723Labels := by rfl

def raw27920 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw27920Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27920step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw27920step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27920step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw27920step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27920step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw27920step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27920 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27920 raw27920Labels = mixedMoment B node3466 node3466Labels := by
  calc
    mixedMoment B raw27920 raw27920Labels = mixedMoment B raw27920step0 raw27920step0Labels := by
      have ha : raw27920step0 = (fun i j => raw27920 (permutation188 i) (permutation5 j)) := by apply Matrix.ext; unfold raw27920step0 raw27920; decide +kernel
      have hl : raw27920step0Labels = raw27920Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27920 raw27920Labels permutation188 permutation5
    mixedMoment B raw27920step0 raw27920step0Labels = mixedMoment B raw27920step1 raw27920step1Labels := by
      have ha : raw27920step1 = -raw27920step0 := by apply Matrix.ext; change ∀ i j, raw27920step1 i j = -(raw27920step0 i j); unfold raw27920step1 raw27920step0; decide +kernel
      have hl : raw27920step1Labels = raw27920step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27920step1 raw27920step1Labels = mixedMoment B raw27920step2 raw27920step2Labels := by
      have ha : raw27920step2 = raw27920step1 := by apply Matrix.ext; unfold raw27920step2 raw27920step1; decide +kernel
      have hl : raw27920step1Labels = labelEmbedding1 ∘ raw27920step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27920step1 raw27920step1Labels raw27920step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3466 node3466Labels := by rfl

def raw27921 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw27921Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27921step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw27921step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27921step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw27921step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27921step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw27921step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27921 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27921 raw27921Labels = mixedMoment B node3481 node3481Labels := by
  calc
    mixedMoment B raw27921 raw27921Labels = mixedMoment B raw27921step0 raw27921step0Labels := by
      have hz : ∀ j, raw27921 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27921step0 = (fun i j => raw27921 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27921step0 raw27921; decide +kernel
      have hl : raw27921step0Labels = raw27921Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27921 raw27921Labels permutation346 hz
    mixedMoment B raw27921step0 raw27921step0Labels = mixedMoment B raw27921step1 raw27921step1Labels := by
      have ha : raw27921step1 = (fun i j => raw27921step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27921step1 raw27921step0; decide +kernel
      have hl : raw27921step1Labels = raw27921step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27921step0 raw27921step0Labels permutation149 permutation7
    mixedMoment B raw27921step1 raw27921step1Labels = mixedMoment B raw27921step2 raw27921step2Labels := by
      have ha : raw27921step2 = raw27921step1 := by apply Matrix.ext; unfold raw27921step2 raw27921step1; decide +kernel
      have hl : raw27921step1Labels = labelEmbedding1 ∘ raw27921step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27921step1 raw27921step1Labels raw27921step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3481 node3481Labels := by rfl

def raw27922 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw27922Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27922step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw27922step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27922step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw27922step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27922step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw27922step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27922step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw27922step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27922 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27922 raw27922Labels = mixedMoment B node3543 node3543Labels := by
  calc
    mixedMoment B raw27922 raw27922Labels = mixedMoment B raw27922step0 raw27922step0Labels := by
      have hz : ∀ j, raw27922 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27922step0 = (fun i j => raw27922 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27922step0 raw27922; decide +kernel
      have hl : raw27922step0Labels = raw27922Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27922 raw27922Labels permutation346 hz
    mixedMoment B raw27922step0 raw27922step0Labels = mixedMoment B raw27922step1 raw27922step1Labels := by
      have ha : raw27922step1 = (fun i j => raw27922step0 (permutation44 i) (permutation5 j)) := by apply Matrix.ext; unfold raw27922step1 raw27922step0; decide +kernel
      have hl : raw27922step1Labels = raw27922step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27922step0 raw27922step0Labels permutation44 permutation5
    mixedMoment B raw27922step1 raw27922step1Labels = mixedMoment B raw27922step2 raw27922step2Labels := by
      have ha : raw27922step2 = -raw27922step1 := by apply Matrix.ext; change ∀ i j, raw27922step2 i j = -(raw27922step1 i j); unfold raw27922step2 raw27922step1; decide +kernel
      have hl : raw27922step2Labels = raw27922step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27922step2 raw27922step2Labels = mixedMoment B raw27922step3 raw27922step3Labels := by
      have ha : raw27922step3 = raw27922step2 := by apply Matrix.ext; unfold raw27922step3 raw27922step2; decide +kernel
      have hl : raw27922step2Labels = labelEmbedding1 ∘ raw27922step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27922step2 raw27922step2Labels raw27922step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3543 node3543Labels := by rfl

def raw27923 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw27923Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27923step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw27923step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27923step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0]]
def raw27923step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27923step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw27923step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27923step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw27923step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27923 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27923 raw27923Labels = mixedMoment B node3625 node3625Labels := by
  calc
    mixedMoment B raw27923 raw27923Labels = mixedMoment B raw27923step0 raw27923step0Labels := by
      have hz : ∀ j, raw27923 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27923step0 = (fun i j => raw27923 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27923step0 raw27923; decide +kernel
      have hl : raw27923step0Labels = raw27923Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27923 raw27923Labels permutation346 hz
    mixedMoment B raw27923step0 raw27923step0Labels = mixedMoment B raw27923step1 raw27923step1Labels := by
      have ha : raw27923step1 = (fun i j => raw27923step0 (permutation48 i) (permutation5 j)) := by apply Matrix.ext; unfold raw27923step1 raw27923step0; decide +kernel
      have hl : raw27923step1Labels = raw27923step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27923step0 raw27923step0Labels permutation48 permutation5
    mixedMoment B raw27923step1 raw27923step1Labels = mixedMoment B raw27923step2 raw27923step2Labels := by
      have ha : raw27923step2 = -raw27923step1 := by apply Matrix.ext; change ∀ i j, raw27923step2 i j = -(raw27923step1 i j); unfold raw27923step2 raw27923step1; decide +kernel
      have hl : raw27923step2Labels = raw27923step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27923step2 raw27923step2Labels = mixedMoment B raw27923step3 raw27923step3Labels := by
      have ha : raw27923step3 = raw27923step2 := by apply Matrix.ext; unfold raw27923step3 raw27923step2; decide +kernel
      have hl : raw27923step2Labels = labelEmbedding1 ∘ raw27923step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27923step2 raw27923step2Labels raw27923step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3625 node3625Labels := by rfl

def raw27924 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw27924Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27924step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw27924step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27924step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw27924step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27924step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw27924step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27924 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27924 raw27924Labels = mixedMoment B node1670 node1670Labels := by
  calc
    mixedMoment B raw27924 raw27924Labels = mixedMoment B raw27924step0 raw27924step0Labels := by
      have ha : raw27924step0 = (fun i j => raw27924 (permutation166 i) (permutation5 j)) := by apply Matrix.ext; unfold raw27924step0 raw27924; decide +kernel
      have hl : raw27924step0Labels = raw27924Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27924 raw27924Labels permutation166 permutation5
    mixedMoment B raw27924step0 raw27924step0Labels = mixedMoment B raw27924step1 raw27924step1Labels := by
      have ha : raw27924step1 = -raw27924step0 := by apply Matrix.ext; change ∀ i j, raw27924step1 i j = -(raw27924step0 i j); unfold raw27924step1 raw27924step0; decide +kernel
      have hl : raw27924step1Labels = raw27924step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27924step1 raw27924step1Labels = mixedMoment B raw27924step2 raw27924step2Labels := by
      have ha : raw27924step2 = raw27924step1 := by apply Matrix.ext; unfold raw27924step2 raw27924step1; decide +kernel
      have hl : raw27924step1Labels = labelEmbedding1 ∘ raw27924step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27924step1 raw27924step1Labels raw27924step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1670 node1670Labels := by rfl

def raw27925 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw27925Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27925step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw27925step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27925step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw27925step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27925step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw27925step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27925 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27925 raw27925Labels = mixedMoment B node3408 node3408Labels := by
  calc
    mixedMoment B raw27925 raw27925Labels = mixedMoment B raw27925step0 raw27925step0Labels := by
      have ha : raw27925step0 = (fun i j => raw27925 (permutation166 i) (permutation5 j)) := by apply Matrix.ext; unfold raw27925step0 raw27925; decide +kernel
      have hl : raw27925step0Labels = raw27925Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27925 raw27925Labels permutation166 permutation5
    mixedMoment B raw27925step0 raw27925step0Labels = mixedMoment B raw27925step1 raw27925step1Labels := by
      have ha : raw27925step1 = -raw27925step0 := by apply Matrix.ext; change ∀ i j, raw27925step1 i j = -(raw27925step0 i j); unfold raw27925step1 raw27925step0; decide +kernel
      have hl : raw27925step1Labels = raw27925step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27925step1 raw27925step1Labels = mixedMoment B raw27925step2 raw27925step2Labels := by
      have ha : raw27925step2 = raw27925step1 := by apply Matrix.ext; unfold raw27925step2 raw27925step1; decide +kernel
      have hl : raw27925step1Labels = labelEmbedding1 ∘ raw27925step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27925step1 raw27925step1Labels raw27925step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3408 node3408Labels := by rfl

def raw27926 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw27926Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27926step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw27926step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27926step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw27926step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27926 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27926 raw27926Labels = mixedMoment B node3455 node3455Labels := by
  calc
    mixedMoment B raw27926 raw27926Labels = mixedMoment B raw27926step0 raw27926step0Labels := by
      have ha : raw27926step0 = (fun i j => raw27926 (permutation680 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27926step0 raw27926; decide +kernel
      have hl : raw27926step0Labels = raw27926Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27926 raw27926Labels permutation680 permutation7
    mixedMoment B raw27926step0 raw27926step0Labels = mixedMoment B raw27926step1 raw27926step1Labels := by
      have ha : raw27926step1 = raw27926step0 := by apply Matrix.ext; unfold raw27926step1 raw27926step0; decide +kernel
      have hl : raw27926step0Labels = labelEmbedding1 ∘ raw27926step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27926step0 raw27926step0Labels raw27926step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3455 node3455Labels := by rfl

def raw27927 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw27927Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27927step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw27927step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27927step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw27927step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27927step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw27927step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27927 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27927 raw27927Labels = mixedMoment B node3519 node3519Labels := by
  calc
    mixedMoment B raw27927 raw27927Labels = mixedMoment B raw27927step0 raw27927step0Labels := by
      have ha : raw27927step0 = (fun i j => raw27927 (permutation226 i) (permutation5 j)) := by apply Matrix.ext; unfold raw27927step0 raw27927; decide +kernel
      have hl : raw27927step0Labels = raw27927Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27927 raw27927Labels permutation226 permutation5
    mixedMoment B raw27927step0 raw27927step0Labels = mixedMoment B raw27927step1 raw27927step1Labels := by
      have ha : raw27927step1 = -raw27927step0 := by apply Matrix.ext; change ∀ i j, raw27927step1 i j = -(raw27927step0 i j); unfold raw27927step1 raw27927step0; decide +kernel
      have hl : raw27927step1Labels = raw27927step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27927step1 raw27927step1Labels = mixedMoment B raw27927step2 raw27927step2Labels := by
      have ha : raw27927step2 = raw27927step1 := by apply Matrix.ext; unfold raw27927step2 raw27927step1; decide +kernel
      have hl : raw27927step1Labels = labelEmbedding1 ∘ raw27927step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27927step1 raw27927step1Labels raw27927step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3519 node3519Labels := by rfl

def raw27928 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw27928Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27928step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1]]
def raw27928step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27928step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw27928step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27928step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw27928step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27928 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27928 raw27928Labels = mixedMoment B node3605 node3605Labels := by
  calc
    mixedMoment B raw27928 raw27928Labels = mixedMoment B raw27928step0 raw27928step0Labels := by
      have ha : raw27928step0 = (fun i j => raw27928 (permutation169 i) (permutation5 j)) := by apply Matrix.ext; unfold raw27928step0 raw27928; decide +kernel
      have hl : raw27928step0Labels = raw27928Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27928 raw27928Labels permutation169 permutation5
    mixedMoment B raw27928step0 raw27928step0Labels = mixedMoment B raw27928step1 raw27928step1Labels := by
      have ha : raw27928step1 = -raw27928step0 := by apply Matrix.ext; change ∀ i j, raw27928step1 i j = -(raw27928step0 i j); unfold raw27928step1 raw27928step0; decide +kernel
      have hl : raw27928step1Labels = raw27928step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27928step1 raw27928step1Labels = mixedMoment B raw27928step2 raw27928step2Labels := by
      have ha : raw27928step2 = raw27928step1 := by apply Matrix.ext; unfold raw27928step2 raw27928step1; decide +kernel
      have hl : raw27928step1Labels = labelEmbedding1 ∘ raw27928step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27928step1 raw27928step1Labels raw27928step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3605 node3605Labels := by rfl

def raw27929 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw27929Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27929step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw27929step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27929step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![-1, -2, 3], ![-2, 1, 1]]
def raw27929step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27929step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw27929step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27929step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw27929step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27929 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27929 raw27929Labels = mixedMoment B node1676 node1676Labels := by
  calc
    mixedMoment B raw27929 raw27929Labels = mixedMoment B raw27929step0 raw27929step0Labels := by
      have hz : ∀ j, raw27929 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27929step0 = (fun i j => raw27929 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27929step0 raw27929; decide +kernel
      have hl : raw27929step0Labels = raw27929Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27929 raw27929Labels permutation346 hz
    mixedMoment B raw27929step0 raw27929step0Labels = mixedMoment B raw27929step1 raw27929step1Labels := by
      have ha : raw27929step1 = (fun i j => raw27929step0 (permutation35 i) (permutation5 j)) := by apply Matrix.ext; unfold raw27929step1 raw27929step0; decide +kernel
      have hl : raw27929step1Labels = raw27929step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27929step0 raw27929step0Labels permutation35 permutation5
    mixedMoment B raw27929step1 raw27929step1Labels = mixedMoment B raw27929step2 raw27929step2Labels := by
      have ha : raw27929step2 = -raw27929step1 := by apply Matrix.ext; change ∀ i j, raw27929step2 i j = -(raw27929step1 i j); unfold raw27929step2 raw27929step1; decide +kernel
      have hl : raw27929step2Labels = raw27929step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27929step2 raw27929step2Labels = mixedMoment B raw27929step3 raw27929step3Labels := by
      have ha : raw27929step3 = raw27929step2 := by apply Matrix.ext; unfold raw27929step3 raw27929step2; decide +kernel
      have hl : raw27929step2Labels = labelEmbedding1 ∘ raw27929step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27929step2 raw27929step2Labels raw27929step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1676 node1676Labels := by rfl

def raw27930 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw27930Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27930step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw27930step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27930step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -1, 1], ![-1, -2, 3], ![-2, 1, 1]]
def raw27930step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27930step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw27930step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27930step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw27930step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27930 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27930 raw27930Labels = mixedMoment B node3413 node3413Labels := by
  calc
    mixedMoment B raw27930 raw27930Labels = mixedMoment B raw27930step0 raw27930step0Labels := by
      have hz : ∀ j, raw27930 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27930step0 = (fun i j => raw27930 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27930step0 raw27930; decide +kernel
      have hl : raw27930step0Labels = raw27930Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27930 raw27930Labels permutation346 hz
    mixedMoment B raw27930step0 raw27930step0Labels = mixedMoment B raw27930step1 raw27930step1Labels := by
      have ha : raw27930step1 = (fun i j => raw27930step0 (permutation35 i) (permutation5 j)) := by apply Matrix.ext; unfold raw27930step1 raw27930step0; decide +kernel
      have hl : raw27930step1Labels = raw27930step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27930step0 raw27930step0Labels permutation35 permutation5
    mixedMoment B raw27930step1 raw27930step1Labels = mixedMoment B raw27930step2 raw27930step2Labels := by
      have ha : raw27930step2 = -raw27930step1 := by apply Matrix.ext; change ∀ i j, raw27930step2 i j = -(raw27930step1 i j); unfold raw27930step2 raw27930step1; decide +kernel
      have hl : raw27930step2Labels = raw27930step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27930step2 raw27930step2Labels = mixedMoment B raw27930step3 raw27930step3Labels := by
      have ha : raw27930step3 = raw27930step2 := by apply Matrix.ext; unfold raw27930step3 raw27930step2; decide +kernel
      have hl : raw27930step2Labels = labelEmbedding1 ∘ raw27930step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27930step2 raw27930step2Labels raw27930step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3413 node3413Labels := by rfl

def raw27931 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw27931Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27931step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 1, -1], ![0, -1, 1], ![-1, -2, 3], ![-2, 1, 1]]
def raw27931step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27931step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw27931step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27931step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw27931step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27931 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27931 raw27931Labels = mixedMoment B node3451 node3451Labels := by
  calc
    mixedMoment B raw27931 raw27931Labels = mixedMoment B raw27931step0 raw27931step0Labels := by
      have ha : raw27931step0 = (fun i j => raw27931 (permutation179 i) (permutation5 j)) := by apply Matrix.ext; unfold raw27931step0 raw27931; decide +kernel
      have hl : raw27931step0Labels = raw27931Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27931 raw27931Labels permutation179 permutation5
    mixedMoment B raw27931step0 raw27931step0Labels = mixedMoment B raw27931step1 raw27931step1Labels := by
      have ha : raw27931step1 = -raw27931step0 := by apply Matrix.ext; change ∀ i j, raw27931step1 i j = -(raw27931step0 i j); unfold raw27931step1 raw27931step0; decide +kernel
      have hl : raw27931step1Labels = raw27931step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27931step1 raw27931step1Labels = mixedMoment B raw27931step2 raw27931step2Labels := by
      have ha : raw27931step2 = raw27931step1 := by apply Matrix.ext; unfold raw27931step2 raw27931step1; decide +kernel
      have hl : raw27931step1Labels = labelEmbedding1 ∘ raw27931step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27931step1 raw27931step1Labels raw27931step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3451 node3451Labels := by rfl

def raw27932 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![0, 1, -1], ![3, -1, -2]]
def raw27932Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27932step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![0, 1, -1], ![3, -1, -2]]
def raw27932step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27932step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![-1, -2, 3], ![-2, 1, 1]]
def raw27932step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27932step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw27932step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27932step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw27932step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27932 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27932 raw27932Labels = mixedMoment B node3523 node3523Labels := by
  calc
    mixedMoment B raw27932 raw27932Labels = mixedMoment B raw27932step0 raw27932step0Labels := by
      have hz : ∀ j, raw27932 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27932step0 = (fun i j => raw27932 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27932step0 raw27932; decide +kernel
      have hl : raw27932step0Labels = raw27932Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27932 raw27932Labels permutation346 hz
    mixedMoment B raw27932step0 raw27932step0Labels = mixedMoment B raw27932step1 raw27932step1Labels := by
      have ha : raw27932step1 = (fun i j => raw27932step0 (permutation45 i) (permutation5 j)) := by apply Matrix.ext; unfold raw27932step1 raw27932step0; decide +kernel
      have hl : raw27932step1Labels = raw27932step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27932step0 raw27932step0Labels permutation45 permutation5
    mixedMoment B raw27932step1 raw27932step1Labels = mixedMoment B raw27932step2 raw27932step2Labels := by
      have ha : raw27932step2 = -raw27932step1 := by apply Matrix.ext; change ∀ i j, raw27932step2 i j = -(raw27932step1 i j); unfold raw27932step2 raw27932step1; decide +kernel
      have hl : raw27932step2Labels = raw27932step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27932step2 raw27932step2Labels = mixedMoment B raw27932step3 raw27932step3Labels := by
      have ha : raw27932step3 = raw27932step2 := by apply Matrix.ext; unfold raw27932step3 raw27932step2; decide +kernel
      have hl : raw27932step2Labels = labelEmbedding1 ∘ raw27932step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27932step2 raw27932step2Labels raw27932step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3523 node3523Labels := by rfl

def raw27933 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw27933Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27933step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw27933step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27933step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-2, 1, 1]]
def raw27933step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27933step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]
def raw27933step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27933step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]
def raw27933step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27933 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27933 raw27933Labels = mixedMoment B node3606 node3606Labels := by
  calc
    mixedMoment B raw27933 raw27933Labels = mixedMoment B raw27933step0 raw27933step0Labels := by
      have hz : ∀ j, raw27933 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27933step0 = (fun i j => raw27933 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27933step0 raw27933; decide +kernel
      have hl : raw27933step0Labels = raw27933Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27933 raw27933Labels permutation346 hz
    mixedMoment B raw27933step0 raw27933step0Labels = mixedMoment B raw27933step1 raw27933step1Labels := by
      have ha : raw27933step1 = (fun i j => raw27933step0 (permutation35 i) (permutation5 j)) := by apply Matrix.ext; unfold raw27933step1 raw27933step0; decide +kernel
      have hl : raw27933step1Labels = raw27933step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27933step0 raw27933step0Labels permutation35 permutation5
    mixedMoment B raw27933step1 raw27933step1Labels = mixedMoment B raw27933step2 raw27933step2Labels := by
      have ha : raw27933step2 = -raw27933step1 := by apply Matrix.ext; change ∀ i j, raw27933step2 i j = -(raw27933step1 i j); unfold raw27933step2 raw27933step1; decide +kernel
      have hl : raw27933step2Labels = raw27933step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27933step2 raw27933step2Labels = mixedMoment B raw27933step3 raw27933step3Labels := by
      have ha : raw27933step3 = raw27933step2 := by apply Matrix.ext; unfold raw27933step3 raw27933step2; decide +kernel
      have hl : raw27933step2Labels = labelEmbedding1 ∘ raw27933step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27933step2 raw27933step2Labels raw27933step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3606 node3606Labels := by rfl

def raw27934 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw27934Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27934step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw27934step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27934step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -2, 3]]
def raw27934step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27934step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw27934step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27934step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw27934step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27934 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27934 raw27934Labels = mixedMoment B node1689 node1689Labels := by
  calc
    mixedMoment B raw27934 raw27934Labels = mixedMoment B raw27934step0 raw27934step0Labels := by
      have hz : ∀ j, raw27934 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27934step0 = (fun i j => raw27934 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27934step0 raw27934; decide +kernel
      have hl : raw27934step0Labels = raw27934Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27934 raw27934Labels permutation346 hz
    mixedMoment B raw27934step0 raw27934step0Labels = mixedMoment B raw27934step1 raw27934step1Labels := by
      have ha : raw27934step1 = (fun i j => raw27934step0 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw27934step1 raw27934step0; decide +kernel
      have hl : raw27934step1Labels = raw27934step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27934step0 raw27934step0Labels permutation32 permutation5
    mixedMoment B raw27934step1 raw27934step1Labels = mixedMoment B raw27934step2 raw27934step2Labels := by
      have ha : raw27934step2 = -raw27934step1 := by apply Matrix.ext; change ∀ i j, raw27934step2 i j = -(raw27934step1 i j); unfold raw27934step2 raw27934step1; decide +kernel
      have hl : raw27934step2Labels = raw27934step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27934step2 raw27934step2Labels = mixedMoment B raw27934step3 raw27934step3Labels := by
      have ha : raw27934step3 = raw27934step2 := by apply Matrix.ext; unfold raw27934step3 raw27934step2; decide +kernel
      have hl : raw27934step2Labels = labelEmbedding1 ∘ raw27934step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27934step2 raw27934step2Labels raw27934step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1689 node1689Labels := by rfl

def raw27935 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw27935Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27935step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw27935step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27935step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![-1, 1, 0], ![-1, -1, 2], ![-1, -2, 3]]
def raw27935step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27935step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw27935step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27935step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw27935step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27935 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27935 raw27935Labels = mixedMoment B node3419 node3419Labels := by
  calc
    mixedMoment B raw27935 raw27935Labels = mixedMoment B raw27935step0 raw27935step0Labels := by
      have hz : ∀ j, raw27935 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27935step0 = (fun i j => raw27935 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27935step0 raw27935; decide +kernel
      have hl : raw27935step0Labels = raw27935Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27935 raw27935Labels permutation346 hz
    mixedMoment B raw27935step0 raw27935step0Labels = mixedMoment B raw27935step1 raw27935step1Labels := by
      have ha : raw27935step1 = (fun i j => raw27935step0 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw27935step1 raw27935step0; decide +kernel
      have hl : raw27935step1Labels = raw27935step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27935step0 raw27935step0Labels permutation32 permutation5
    mixedMoment B raw27935step1 raw27935step1Labels = mixedMoment B raw27935step2 raw27935step2Labels := by
      have ha : raw27935step2 = -raw27935step1 := by apply Matrix.ext; change ∀ i j, raw27935step2 i j = -(raw27935step1 i j); unfold raw27935step2 raw27935step1; decide +kernel
      have hl : raw27935step2Labels = raw27935step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27935step2 raw27935step2Labels = mixedMoment B raw27935step3 raw27935step3Labels := by
      have ha : raw27935step3 = raw27935step2 := by apply Matrix.ext; unfold raw27935step3 raw27935step2; decide +kernel
      have hl : raw27935step2Labels = labelEmbedding1 ∘ raw27935step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27935step2 raw27935step2Labels raw27935step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3419 node3419Labels := by rfl

def raw27936 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw27936Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27936step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw27936step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27936step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw27936step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27936 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27936 raw27936Labels = mixedMoment B node3408 node3408Labels := by
  calc
    mixedMoment B raw27936 raw27936Labels = mixedMoment B raw27936step0 raw27936step0Labels := by
      have ha : raw27936step0 = (fun i j => raw27936 (permutation682 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27936step0 raw27936; decide +kernel
      have hl : raw27936step0Labels = raw27936Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27936 raw27936Labels permutation682 permutation7
    mixedMoment B raw27936step0 raw27936step0Labels = mixedMoment B raw27936step1 raw27936step1Labels := by
      have ha : raw27936step1 = raw27936step0 := by apply Matrix.ext; unfold raw27936step1 raw27936step0; decide +kernel
      have hl : raw27936step0Labels = labelEmbedding1 ∘ raw27936step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27936step0 raw27936step0Labels raw27936step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3408 node3408Labels := by rfl

def raw27937 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![2, -1, -1], ![3, -1, -2]]
def raw27937Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27937step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![2, -1, -1], ![3, -1, -2]]
def raw27937step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27937step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw27937step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27937step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw27937step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27937 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27937 raw27937Labels = mixedMoment B node3420 node3420Labels := by
  calc
    mixedMoment B raw27937 raw27937Labels = mixedMoment B raw27937step0 raw27937step0Labels := by
      have hz : ∀ j, raw27937 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27937step0 = (fun i j => raw27937 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27937step0 raw27937; decide +kernel
      have hl : raw27937step0Labels = raw27937Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27937 raw27937Labels permutation346 hz
    mixedMoment B raw27937step0 raw27937step0Labels = mixedMoment B raw27937step1 raw27937step1Labels := by
      have ha : raw27937step1 = (fun i j => raw27937step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27937step1 raw27937step0; decide +kernel
      have hl : raw27937step1Labels = raw27937step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27937step0 raw27937step0Labels permutation149 permutation7
    mixedMoment B raw27937step1 raw27937step1Labels = mixedMoment B raw27937step2 raw27937step2Labels := by
      have ha : raw27937step2 = raw27937step1 := by apply Matrix.ext; unfold raw27937step2 raw27937step1; decide +kernel
      have hl : raw27937step1Labels = labelEmbedding1 ∘ raw27937step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27937step1 raw27937step1Labels raw27937step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3420 node3420Labels := by rfl

def raw27938 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw27938Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27938step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw27938step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27938step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, -1, 2]]
def raw27938step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27938step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]
def raw27938step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27938step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]
def raw27938step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27938 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27938 raw27938Labels = mixedMoment B node3612 node3612Labels := by
  calc
    mixedMoment B raw27938 raw27938Labels = mixedMoment B raw27938step0 raw27938step0Labels := by
      have hz : ∀ j, raw27938 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27938step0 = (fun i j => raw27938 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27938step0 raw27938; decide +kernel
      have hl : raw27938step0Labels = raw27938Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27938 raw27938Labels permutation346 hz
    mixedMoment B raw27938step0 raw27938step0Labels = mixedMoment B raw27938step1 raw27938step1Labels := by
      have ha : raw27938step1 = (fun i j => raw27938step0 (permutation36 i) (permutation5 j)) := by apply Matrix.ext; unfold raw27938step1 raw27938step0; decide +kernel
      have hl : raw27938step1Labels = raw27938step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27938step0 raw27938step0Labels permutation36 permutation5
    mixedMoment B raw27938step1 raw27938step1Labels = mixedMoment B raw27938step2 raw27938step2Labels := by
      have ha : raw27938step2 = -raw27938step1 := by apply Matrix.ext; change ∀ i j, raw27938step2 i j = -(raw27938step1 i j); unfold raw27938step2 raw27938step1; decide +kernel
      have hl : raw27938step2Labels = raw27938step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27938step2 raw27938step2Labels = mixedMoment B raw27938step3 raw27938step3Labels := by
      have ha : raw27938step3 = raw27938step2 := by apply Matrix.ext; unfold raw27938step3 raw27938step2; decide +kernel
      have hl : raw27938step2Labels = labelEmbedding1 ∘ raw27938step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27938step2 raw27938step2Labels raw27938step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3612 node3612Labels := by rfl

def raw27939 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![4, -2, -2]]
def raw27939Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27939step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![4, -2, -2]]
def raw27939step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27939step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, -2, 4]]
def raw27939step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27939step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw27939step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27939step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw27939step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27939 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27939 raw27939Labels = mixedMoment B node1672 node1672Labels := by
  calc
    mixedMoment B raw27939 raw27939Labels = mixedMoment B raw27939step0 raw27939step0Labels := by
      have hz : ∀ j, raw27939 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27939step0 = (fun i j => raw27939 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27939step0 raw27939; decide +kernel
      have hl : raw27939step0Labels = raw27939Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27939 raw27939Labels permutation346 hz
    mixedMoment B raw27939step0 raw27939step0Labels = mixedMoment B raw27939step1 raw27939step1Labels := by
      have ha : raw27939step1 = (fun i j => raw27939step0 (permutation34 i) (permutation5 j)) := by apply Matrix.ext; unfold raw27939step1 raw27939step0; decide +kernel
      have hl : raw27939step1Labels = raw27939step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27939step0 raw27939step0Labels permutation34 permutation5
    mixedMoment B raw27939step1 raw27939step1Labels = mixedMoment B raw27939step2 raw27939step2Labels := by
      have ha : raw27939step2 = -raw27939step1 := by apply Matrix.ext; change ∀ i j, raw27939step2 i j = -(raw27939step1 i j); unfold raw27939step2 raw27939step1; decide +kernel
      have hl : raw27939step2Labels = raw27939step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27939step2 raw27939step2Labels = mixedMoment B raw27939step3 raw27939step3Labels := by
      have ha : raw27939step3 = raw27939step2 := by apply Matrix.ext; unfold raw27939step3 raw27939step2; decide +kernel
      have hl : raw27939step2Labels = labelEmbedding1 ∘ raw27939step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27939step2 raw27939step2Labels raw27939step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1672 node1672Labels := by rfl

def raw27940 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![4, -2, -2]]
def raw27940Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27940step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![4, -2, -2]]
def raw27940step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27940step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw27940step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27940step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw27940step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27940 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27940 raw27940Labels = mixedMoment B node3272 node3272Labels := by
  calc
    mixedMoment B raw27940 raw27940Labels = mixedMoment B raw27940step0 raw27940step0Labels := by
      have hz : ∀ j, raw27940 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27940step0 = (fun i j => raw27940 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27940step0 raw27940; decide +kernel
      have hl : raw27940step0Labels = raw27940Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27940 raw27940Labels permutation346 hz
    mixedMoment B raw27940step0 raw27940step0Labels = mixedMoment B raw27940step1 raw27940step1Labels := by
      have ha : raw27940step1 = (fun i j => raw27940step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27940step1 raw27940step0; decide +kernel
      have hl : raw27940step1Labels = raw27940step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27940step0 raw27940step0Labels permutation151 permutation7
    mixedMoment B raw27940step1 raw27940step1Labels = mixedMoment B raw27940step2 raw27940step2Labels := by
      have ha : raw27940step2 = raw27940step1 := by apply Matrix.ext; unfold raw27940step2 raw27940step1; decide +kernel
      have hl : raw27940step1Labels = labelEmbedding1 ∘ raw27940step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27940step1 raw27940step1Labels raw27940step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3272 node3272Labels := by rfl

def raw27941 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![4, -2, -2]]
def raw27941Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27941step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw27941step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27941step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw27941step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27941 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27941 raw27941Labels = mixedMoment B node3260 node3260Labels := by
  calc
    mixedMoment B raw27941 raw27941Labels = mixedMoment B raw27941step0 raw27941step0Labels := by
      have ha : raw27941step0 = (fun i j => raw27941 (permutation682 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27941step0 raw27941; decide +kernel
      have hl : raw27941step0Labels = raw27941Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27941 raw27941Labels permutation682 permutation7
    mixedMoment B raw27941step0 raw27941step0Labels = mixedMoment B raw27941step1 raw27941step1Labels := by
      have ha : raw27941step1 = raw27941step0 := by apply Matrix.ext; unfold raw27941step1 raw27941step0; decide +kernel
      have hl : raw27941step0Labels = labelEmbedding1 ∘ raw27941step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27941step0 raw27941step0Labels raw27941step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3260 node3260Labels := by rfl

def raw27942 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw27942Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27942step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw27942step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27942step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw27942step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27942step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw27942step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27942 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27942 raw27942Labels = mixedMoment B node3273 node3273Labels := by
  calc
    mixedMoment B raw27942 raw27942Labels = mixedMoment B raw27942step0 raw27942step0Labels := by
      have hz : ∀ j, raw27942 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27942step0 = (fun i j => raw27942 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27942step0 raw27942; decide +kernel
      have hl : raw27942step0Labels = raw27942Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27942 raw27942Labels permutation346 hz
    mixedMoment B raw27942step0 raw27942step0Labels = mixedMoment B raw27942step1 raw27942step1Labels := by
      have ha : raw27942step1 = (fun i j => raw27942step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27942step1 raw27942step0; decide +kernel
      have hl : raw27942step1Labels = raw27942step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27942step0 raw27942step0Labels permutation149 permutation7
    mixedMoment B raw27942step1 raw27942step1Labels = mixedMoment B raw27942step2 raw27942step2Labels := by
      have ha : raw27942step2 = raw27942step1 := by apply Matrix.ext; unfold raw27942step2 raw27942step1; decide +kernel
      have hl : raw27942step1Labels = labelEmbedding1 ∘ raw27942step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27942step1 raw27942step1Labels raw27942step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3273 node3273Labels := by rfl

def raw27943 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![4, -2, -2]]
def raw27943Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27943step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![4, -2, -2]]
def raw27943step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27943step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw27943step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27943step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw27943step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27943 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27943 raw27943Labels = mixedMoment B node3291 node3291Labels := by
  calc
    mixedMoment B raw27943 raw27943Labels = mixedMoment B raw27943step0 raw27943step0Labels := by
      have hz : ∀ j, raw27943 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27943step0 = (fun i j => raw27943 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27943step0 raw27943; decide +kernel
      have hl : raw27943step0Labels = raw27943Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27943 raw27943Labels permutation346 hz
    mixedMoment B raw27943step0 raw27943step0Labels = mixedMoment B raw27943step1 raw27943step1Labels := by
      have ha : raw27943step1 = (fun i j => raw27943step0 (permutation143 i) (permutation5 j)) := by apply Matrix.ext; unfold raw27943step1 raw27943step0; decide +kernel
      have hl : raw27943step1Labels = raw27943step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27943step0 raw27943step0Labels permutation143 permutation5
    mixedMoment B raw27943step1 raw27943step1Labels = mixedMoment B raw27943step2 raw27943step2Labels := by
      have ha : raw27943step2 = raw27943step1 := by apply Matrix.ext; unfold raw27943step2 raw27943step1; decide +kernel
      have hl : raw27943step1Labels = labelEmbedding1 ∘ raw27943step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27943step1 raw27943step1Labels raw27943step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3291 node3291Labels := by rfl

def raw27944 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw27944Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27944step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw27944step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27944step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw27944step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27944step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw27944step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27944 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27944 raw27944Labels = mixedMoment B node2514 node2514Labels := by
  calc
    mixedMoment B raw27944 raw27944Labels = mixedMoment B raw27944step0 raw27944step0Labels := by
      have hz : ∀ j, raw27944 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27944step0 = (fun i j => raw27944 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27944step0 raw27944; decide +kernel
      have hl : raw27944step0Labels = raw27944Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27944 raw27944Labels permutation346 hz
    mixedMoment B raw27944step0 raw27944step0Labels = mixedMoment B raw27944step1 raw27944step1Labels := by
      have ha : raw27944step1 = (fun i j => raw27944step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27944step1 raw27944step0; decide +kernel
      have hl : raw27944step1Labels = raw27944step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27944step0 raw27944step0Labels permutation149 permutation2
    mixedMoment B raw27944step1 raw27944step1Labels = mixedMoment B raw27944step2 raw27944step2Labels := by
      have ha : raw27944step2 = -raw27944step1 := by apply Matrix.ext; change ∀ i j, raw27944step2 i j = -(raw27944step1 i j); unfold raw27944step2 raw27944step1; decide +kernel
      have hl : raw27944step2Labels = raw27944step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2514 node2514Labels := by rfl

def raw27945 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw27945Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27945step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw27945step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27945step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw27945step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27945step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27945step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27945 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27945 raw27945Labels = mixedMoment B node2485 node2485Labels := by
  calc
    mixedMoment B raw27945 raw27945Labels = mixedMoment B raw27945step0 raw27945step0Labels := by
      have hz : ∀ j, raw27945 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27945step0 = (fun i j => raw27945 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27945step0 raw27945; decide +kernel
      have hl : raw27945step0Labels = raw27945Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27945 raw27945Labels permutation346 hz
    mixedMoment B raw27945step0 raw27945step0Labels = mixedMoment B raw27945step1 raw27945step1Labels := by
      have ha : raw27945step1 = (fun i j => raw27945step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27945step1 raw27945step0; decide +kernel
      have hl : raw27945step1Labels = raw27945step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27945step0 raw27945step0Labels permutation149 permutation2
    mixedMoment B raw27945step1 raw27945step1Labels = mixedMoment B raw27945step2 raw27945step2Labels := by
      have ha : raw27945step2 = -raw27945step1 := by apply Matrix.ext; change ∀ i j, raw27945step2 i j = -(raw27945step1 i j); unfold raw27945step2 raw27945step1; decide +kernel
      have hl : raw27945step2Labels = raw27945step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2485 node2485Labels := by rfl

def raw27946 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw27946Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27946step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw27946step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27946step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27946step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27946 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27946 raw27946Labels = mixedMoment B node2429 node2429Labels := by
  calc
    mixedMoment B raw27946 raw27946Labels = mixedMoment B raw27946step0 raw27946step0Labels := by
      have ha : raw27946step0 = (fun i j => raw27946 (permutation680 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27946step0 raw27946; decide +kernel
      have hl : raw27946step0Labels = raw27946Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27946 raw27946Labels permutation680 permutation2
    mixedMoment B raw27946step0 raw27946step0Labels = mixedMoment B raw27946step1 raw27946step1Labels := by
      have ha : raw27946step1 = -raw27946step0 := by apply Matrix.ext; change ∀ i j, raw27946step1 i j = -(raw27946step0 i j); unfold raw27946step1 raw27946step0; decide +kernel
      have hl : raw27946step1Labels = raw27946step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2429 node2429Labels := by rfl

def raw27947 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw27947Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27947step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw27947step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27947step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw27947step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27947step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27947step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27947 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27947 raw27947Labels = mixedMoment B node2485 node2485Labels := by
  calc
    mixedMoment B raw27947 raw27947Labels = mixedMoment B raw27947step0 raw27947step0Labels := by
      have hz : ∀ j, raw27947 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27947step0 = (fun i j => raw27947 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27947step0 raw27947; decide +kernel
      have hl : raw27947step0Labels = raw27947Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27947 raw27947Labels permutation346 hz
    mixedMoment B raw27947step0 raw27947step0Labels = mixedMoment B raw27947step1 raw27947step1Labels := by
      have ha : raw27947step1 = (fun i j => raw27947step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27947step1 raw27947step0; decide +kernel
      have hl : raw27947step1Labels = raw27947step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27947step0 raw27947step0Labels permutation151 permutation2
    mixedMoment B raw27947step1 raw27947step1Labels = mixedMoment B raw27947step2 raw27947step2Labels := by
      have ha : raw27947step2 = -raw27947step1 := by apply Matrix.ext; change ∀ i j, raw27947step2 i j = -(raw27947step1 i j); unfold raw27947step2 raw27947step1; decide +kernel
      have hl : raw27947step2Labels = raw27947step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2485 node2485Labels := by rfl

def raw27948 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![2, -1, -1], ![3, -1, -2]]
def raw27948Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27948step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![2, -1, -1], ![3, -1, -2]]
def raw27948step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27948step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw27948step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27948step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27948step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27948 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27948 raw27948Labels = mixedMoment B node2339 node2339Labels := by
  calc
    mixedMoment B raw27948 raw27948Labels = mixedMoment B raw27948step0 raw27948step0Labels := by
      have hz : ∀ j, raw27948 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27948step0 = (fun i j => raw27948 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27948step0 raw27948; decide +kernel
      have hl : raw27948step0Labels = raw27948Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27948 raw27948Labels permutation346 hz
    mixedMoment B raw27948step0 raw27948step0Labels = mixedMoment B raw27948step1 raw27948step1Labels := by
      have ha : raw27948step1 = (fun i j => raw27948step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27948step1 raw27948step0; decide +kernel
      have hl : raw27948step1Labels = raw27948step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27948step0 raw27948step0Labels permutation149 permutation2
    mixedMoment B raw27948step1 raw27948step1Labels = mixedMoment B raw27948step2 raw27948step2Labels := by
      have ha : raw27948step2 = -raw27948step1 := by apply Matrix.ext; change ∀ i j, raw27948step2 i j = -(raw27948step1 i j); unfold raw27948step2 raw27948step1; decide +kernel
      have hl : raw27948step2Labels = raw27948step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2339 node2339Labels := by rfl

def raw27949 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw27949Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27949step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw27949step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27949step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw27949step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27949step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27949step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27949 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27949 raw27949Labels = mixedMoment B node1136 node1136Labels := by
  calc
    mixedMoment B raw27949 raw27949Labels = mixedMoment B raw27949step0 raw27949step0Labels := by
      have hz : ∀ j, raw27949 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27949step0 = (fun i j => raw27949 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27949step0 raw27949; decide +kernel
      have hl : raw27949step0Labels = raw27949Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27949 raw27949Labels permutation346 hz
    mixedMoment B raw27949step0 raw27949step0Labels = mixedMoment B raw27949step1 raw27949step1Labels := by
      have ha : raw27949step1 = (fun i j => raw27949step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27949step1 raw27949step0; decide +kernel
      have hl : raw27949step1Labels = raw27949step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27949step0 raw27949step0Labels permutation149 permutation2
    mixedMoment B raw27949step1 raw27949step1Labels = mixedMoment B raw27949step2 raw27949step2Labels := by
      have ha : raw27949step2 = -raw27949step1 := by apply Matrix.ext; change ∀ i j, raw27949step2 i j = -(raw27949step1 i j); unfold raw27949step2 raw27949step1; decide +kernel
      have hl : raw27949step2Labels = raw27949step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1136 node1136Labels := by rfl

def raw27950 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![0, 0], ![-1, 1], ![1, -1], ![2, -2]]
def raw27950Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27950step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![1, -1], ![2, -2]]
def raw27950step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27950step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![2, -2], ![1, -1], ![-1, 1], ![-1, 1], ![-1, 1]]
def raw27950step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27950step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw27950step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical27950 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27950 raw27950Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw27950 raw27950Labels = mixedMoment B raw27950step0 raw27950step0Labels := by
      have hz : ∀ j, raw27950 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27950step0 = (fun i j => raw27950 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27950step0 raw27950; decide +kernel
      have hl : raw27950step0Labels = raw27950Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27950 raw27950Labels permutation346 hz
    mixedMoment B raw27950step0 raw27950step0Labels = mixedMoment B raw27950step1 raw27950step1Labels := by
      have ha : raw27950step1 = (fun i j => raw27950step0 (permutation146 i) (permutation0 j)) := by apply Matrix.ext; unfold raw27950step1 raw27950step0; decide +kernel
      have hl : raw27950step1Labels = raw27950step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27950step0 raw27950step0Labels permutation146 permutation0
    mixedMoment B raw27950step1 raw27950step1Labels = mixedMoment B raw27950step2 raw27950step2Labels := by
      have ha : raw27950step2 = -raw27950step1 := by apply Matrix.ext; change ∀ i j, raw27950step2 i j = -(raw27950step1 i j); unfold raw27950step2 raw27950step1; decide +kernel
      have hl : raw27950step2Labels = raw27950step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4091 node4091Labels := by rfl

def raw27951 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw27951Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27951step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw27951step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27951step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw27951step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw27951step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw27951step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw27951step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw27951step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27951 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27951 raw27951Labels = mixedMoment B node5075 node5075Labels := by
  calc
    mixedMoment B raw27951 raw27951Labels = mixedMoment B raw27951step0 raw27951step0Labels := by
      have hz : ∀ j, raw27951 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27951step0 = (fun i j => raw27951 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27951step0 raw27951; decide +kernel
      have hl : raw27951step0Labels = raw27951Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27951 raw27951Labels permutation346 hz
    mixedMoment B raw27951step0 raw27951step0Labels = mixedMoment B raw27951step1 raw27951step1Labels := by
      have ha : raw27951step1 = (fun i j => raw27951step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27951step1 raw27951step0; decide +kernel
      have hl : raw27951step1Labels = raw27951step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27951step0 raw27951step0Labels permutation151 permutation7
    mixedMoment B raw27951step1 raw27951step1Labels = mixedMoment B raw27951step2 raw27951step2Labels := by
      have ha : raw27951step2 = -raw27951step1 := by apply Matrix.ext; change ∀ i j, raw27951step2 i j = -(raw27951step1 i j); unfold raw27951step2 raw27951step1; decide +kernel
      have hl : raw27951step2Labels = raw27951step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27951step2 raw27951step2Labels = mixedMoment B raw27951step3 raw27951step3Labels := by
      have ha : raw27951step3 = raw27951step2 := by apply Matrix.ext; unfold raw27951step3 raw27951step2; decide +kernel
      have hl : raw27951step2Labels = labelEmbedding10 ∘ raw27951step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27951step2 raw27951step2Labels raw27951step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5075 node5075Labels := by rfl

def raw27952 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw27952Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27952step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw27952step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw27952step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw27952step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27952 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27952 raw27952Labels = mixedMoment B node5047 node5047Labels := by
  calc
    mixedMoment B raw27952 raw27952Labels = mixedMoment B raw27952step0 raw27952step0Labels := by
      have ha : raw27952step0 = (fun i j => raw27952 (permutation158 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27952step0 raw27952; decide +kernel
      have hl : raw27952step0Labels = raw27952Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27952 raw27952Labels permutation158 permutation7
    mixedMoment B raw27952step0 raw27952step0Labels = mixedMoment B raw27952step1 raw27952step1Labels := by
      have ha : raw27952step1 = raw27952step0 := by apply Matrix.ext; unfold raw27952step1 raw27952step0; decide +kernel
      have hl : raw27952step0Labels = labelEmbedding10 ∘ raw27952step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27952step0 raw27952step0Labels raw27952step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5047 node5047Labels := by rfl

def raw27953 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, -1, 3]]
def raw27953Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27953step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![1, -1, 0], ![-2, 1, 1], ![-2, -1, 3]]
def raw27953step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27953step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw27953step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw27953step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw27953step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw27953step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw27953step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27953 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27953 raw27953Labels = mixedMoment B node5000 node5000Labels := by
  calc
    mixedMoment B raw27953 raw27953Labels = mixedMoment B raw27953step0 raw27953step0Labels := by
      have hz : ∀ j, raw27953 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27953step0 = (fun i j => raw27953 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27953step0 raw27953; decide +kernel
      have hl : raw27953step0Labels = raw27953Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27953 raw27953Labels permutation346 hz
    mixedMoment B raw27953step0 raw27953step0Labels = mixedMoment B raw27953step1 raw27953step1Labels := by
      have ha : raw27953step1 = (fun i j => raw27953step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27953step1 raw27953step0; decide +kernel
      have hl : raw27953step1Labels = raw27953step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27953step0 raw27953step0Labels permutation151 permutation7
    mixedMoment B raw27953step1 raw27953step1Labels = mixedMoment B raw27953step2 raw27953step2Labels := by
      have ha : raw27953step2 = -raw27953step1 := by apply Matrix.ext; change ∀ i j, raw27953step2 i j = -(raw27953step1 i j); unfold raw27953step2 raw27953step1; decide +kernel
      have hl : raw27953step2Labels = raw27953step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27953step2 raw27953step2Labels = mixedMoment B raw27953step3 raw27953step3Labels := by
      have ha : raw27953step3 = raw27953step2 := by apply Matrix.ext; unfold raw27953step3 raw27953step2; decide +kernel
      have hl : raw27953step2Labels = labelEmbedding10 ∘ raw27953step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27953step2 raw27953step2Labels raw27953step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5000 node5000Labels := by rfl

def raw27954 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-3, 0, 3]]
def raw27954Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27954step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-3, 0, 3]]
def raw27954step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27954step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw27954step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw27954step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw27954step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw27954step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw27954step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27954 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27954 raw27954Labels = mixedMoment B node4741 node4741Labels := by
  calc
    mixedMoment B raw27954 raw27954Labels = mixedMoment B raw27954step0 raw27954step0Labels := by
      have hz : ∀ j, raw27954 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27954step0 = (fun i j => raw27954 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27954step0 raw27954; decide +kernel
      have hl : raw27954step0Labels = raw27954Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27954 raw27954Labels permutation346 hz
    mixedMoment B raw27954step0 raw27954step0Labels = mixedMoment B raw27954step1 raw27954step1Labels := by
      have ha : raw27954step1 = (fun i j => raw27954step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27954step1 raw27954step0; decide +kernel
      have hl : raw27954step1Labels = raw27954step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27954step0 raw27954step0Labels permutation151 permutation7
    mixedMoment B raw27954step1 raw27954step1Labels = mixedMoment B raw27954step2 raw27954step2Labels := by
      have ha : raw27954step2 = -raw27954step1 := by apply Matrix.ext; change ∀ i j, raw27954step2 i j = -(raw27954step1 i j); unfold raw27954step2 raw27954step1; decide +kernel
      have hl : raw27954step2Labels = raw27954step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27954step2 raw27954step2Labels = mixedMoment B raw27954step3 raw27954step3Labels := by
      have ha : raw27954step3 = raw27954step2 := by apply Matrix.ext; unfold raw27954step3 raw27954step2; decide +kernel
      have hl : raw27954step2Labels = labelEmbedding10 ∘ raw27954step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27954step2 raw27954step2Labels raw27954step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4741 node4741Labels := by rfl

def raw27955 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw27955Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27955step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw27955step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27955step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw27955step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw27955step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw27955step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27955 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27955 raw27955Labels = mixedMoment B node4853 node4853Labels := by
  calc
    mixedMoment B raw27955 raw27955Labels = mixedMoment B raw27955step0 raw27955step0Labels := by
      have hz : ∀ j, raw27955 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27955step0 = (fun i j => raw27955 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27955step0 raw27955; decide +kernel
      have hl : raw27955step0Labels = raw27955Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27955 raw27955Labels permutation346 hz
    mixedMoment B raw27955step0 raw27955step0Labels = mixedMoment B raw27955step1 raw27955step1Labels := by
      have ha : raw27955step1 = (fun i j => raw27955step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw27955step1 raw27955step0; decide +kernel
      have hl : raw27955step1Labels = raw27955step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27955step0 raw27955step0Labels permutation32 permutation6
    mixedMoment B raw27955step1 raw27955step1Labels = mixedMoment B raw27955step2 raw27955step2Labels := by
      have ha : raw27955step2 = raw27955step1 := by apply Matrix.ext; unfold raw27955step2 raw27955step1; decide +kernel
      have hl : raw27955step1Labels = labelEmbedding9 ∘ raw27955step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27955step1 raw27955step1Labels raw27955step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4853 node4853Labels := by rfl

def raw27956 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw27956Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27956step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw27956step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw27956step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw27956step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw27956step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw27956step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27956 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27956 raw27956Labels = mixedMoment B node5048 node5048Labels := by
  calc
    mixedMoment B raw27956 raw27956Labels = mixedMoment B raw27956step0 raw27956step0Labels := by
      have ha : raw27956step0 = (fun i j => raw27956 (permutation682 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27956step0 raw27956; decide +kernel
      have hl : raw27956step0Labels = raw27956Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27956 raw27956Labels permutation682 permutation7
    mixedMoment B raw27956step0 raw27956step0Labels = mixedMoment B raw27956step1 raw27956step1Labels := by
      have ha : raw27956step1 = -raw27956step0 := by apply Matrix.ext; change ∀ i j, raw27956step1 i j = -(raw27956step0 i j); unfold raw27956step1 raw27956step0; decide +kernel
      have hl : raw27956step1Labels = raw27956step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27956step1 raw27956step1Labels = mixedMoment B raw27956step2 raw27956step2Labels := by
      have ha : raw27956step2 = raw27956step1 := by apply Matrix.ext; unfold raw27956step2 raw27956step1; decide +kernel
      have hl : raw27956step1Labels = labelEmbedding10 ∘ raw27956step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27956step1 raw27956step1Labels raw27956step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5048 node5048Labels := by rfl

def raw27957 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, -1, 3]]
def raw27957Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27957step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![1, -1, 0], ![-2, 1, 1], ![-2, -1, 3]]
def raw27957step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27957step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![0, -1, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw27957step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw27957step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw27957step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw27957step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw27957step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27957 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27957 raw27957Labels = mixedMoment B node5001 node5001Labels := by
  calc
    mixedMoment B raw27957 raw27957Labels = mixedMoment B raw27957step0 raw27957step0Labels := by
      have hz : ∀ j, raw27957 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27957step0 = (fun i j => raw27957 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27957step0 raw27957; decide +kernel
      have hl : raw27957step0Labels = raw27957Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27957 raw27957Labels permutation346 hz
    mixedMoment B raw27957step0 raw27957step0Labels = mixedMoment B raw27957step1 raw27957step1Labels := by
      have ha : raw27957step1 = (fun i j => raw27957step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27957step1 raw27957step0; decide +kernel
      have hl : raw27957step1Labels = raw27957step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27957step0 raw27957step0Labels permutation151 permutation7
    mixedMoment B raw27957step1 raw27957step1Labels = mixedMoment B raw27957step2 raw27957step2Labels := by
      have ha : raw27957step2 = -raw27957step1 := by apply Matrix.ext; change ∀ i j, raw27957step2 i j = -(raw27957step1 i j); unfold raw27957step2 raw27957step1; decide +kernel
      have hl : raw27957step2Labels = raw27957step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27957step2 raw27957step2Labels = mixedMoment B raw27957step3 raw27957step3Labels := by
      have ha : raw27957step3 = raw27957step2 := by apply Matrix.ext; unfold raw27957step3 raw27957step2; decide +kernel
      have hl : raw27957step2Labels = labelEmbedding10 ∘ raw27957step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27957step2 raw27957step2Labels raw27957step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5001 node5001Labels := by rfl

def raw27958 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-3, 0, 3]]
def raw27958Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27958step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![1, -1, 0], ![-1, 0, 1], ![-3, 0, 3]]
def raw27958step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27958step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw27958step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw27958step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw27958step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw27958step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw27958step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27958 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27958 raw27958Labels = mixedMoment B node4742 node4742Labels := by
  calc
    mixedMoment B raw27958 raw27958Labels = mixedMoment B raw27958step0 raw27958step0Labels := by
      have hz : ∀ j, raw27958 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27958step0 = (fun i j => raw27958 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27958step0 raw27958; decide +kernel
      have hl : raw27958step0Labels = raw27958Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27958 raw27958Labels permutation346 hz
    mixedMoment B raw27958step0 raw27958step0Labels = mixedMoment B raw27958step1 raw27958step1Labels := by
      have ha : raw27958step1 = (fun i j => raw27958step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27958step1 raw27958step0; decide +kernel
      have hl : raw27958step1Labels = raw27958step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27958step0 raw27958step0Labels permutation151 permutation7
    mixedMoment B raw27958step1 raw27958step1Labels = mixedMoment B raw27958step2 raw27958step2Labels := by
      have ha : raw27958step2 = -raw27958step1 := by apply Matrix.ext; change ∀ i j, raw27958step2 i j = -(raw27958step1 i j); unfold raw27958step2 raw27958step1; decide +kernel
      have hl : raw27958step2Labels = raw27958step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27958step2 raw27958step2Labels = mixedMoment B raw27958step3 raw27958step3Labels := by
      have ha : raw27958step3 = raw27958step2 := by apply Matrix.ext; unfold raw27958step3 raw27958step2; decide +kernel
      have hl : raw27958step2Labels = labelEmbedding10 ∘ raw27958step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27958step2 raw27958step2Labels raw27958step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4742 node4742Labels := by rfl

def raw27959 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw27959Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27959step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw27959step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw27959step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw27959step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27959 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27959 raw27959Labels = mixedMoment B node4792 node4792Labels := by
  calc
    mixedMoment B raw27959 raw27959Labels = mixedMoment B raw27959step0 raw27959step0Labels := by
      have ha : raw27959step0 = (fun i j => raw27959 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw27959step0 raw27959; decide +kernel
      have hl : raw27959step0Labels = raw27959Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27959 raw27959Labels permutation152 permutation6
    mixedMoment B raw27959step0 raw27959step0Labels = mixedMoment B raw27959step1 raw27959step1Labels := by
      have ha : raw27959step1 = raw27959step0 := by apply Matrix.ext; unfold raw27959step1 raw27959step0; decide +kernel
      have hl : raw27959step0Labels = labelEmbedding9 ∘ raw27959step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27959step0 raw27959step0Labels raw27959step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4792 node4792Labels := by rfl

def raw27960 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw27960Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27960step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw27960step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw27960step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw27960step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27960 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27960 raw27960Labels = mixedMoment B node5065 node5065Labels := by
  calc
    mixedMoment B raw27960 raw27960Labels = mixedMoment B raw27960step0 raw27960step0Labels := by
      have ha : raw27960step0 = (fun i j => raw27960 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw27960step0 raw27960; decide +kernel
      have hl : raw27960step0Labels = raw27960Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27960 raw27960Labels permutation152 permutation6
    mixedMoment B raw27960step0 raw27960step0Labels = mixedMoment B raw27960step1 raw27960step1Labels := by
      have ha : raw27960step1 = raw27960step0 := by apply Matrix.ext; unfold raw27960step1 raw27960step0; decide +kernel
      have hl : raw27960step0Labels = labelEmbedding9 ∘ raw27960step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27960step0 raw27960step0Labels raw27960step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5065 node5065Labels := by rfl

def raw27961 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, -1, 3]]
def raw27961Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27961step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw27961step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw27961step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27961step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw27961step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27961step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27961 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27961 raw27961Labels = mixedMoment B node4992 node4992Labels := by
  calc
    mixedMoment B raw27961 raw27961Labels = mixedMoment B raw27961step0 raw27961step0Labels := by
      have ha : raw27961step0 = (fun i j => raw27961 (permutation682 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27961step0 raw27961; decide +kernel
      have hl : raw27961step0Labels = raw27961Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27961 raw27961Labels permutation682 permutation7
    mixedMoment B raw27961step0 raw27961step0Labels = mixedMoment B raw27961step1 raw27961step1Labels := by
      have ha : raw27961step1 = -raw27961step0 := by apply Matrix.ext; change ∀ i j, raw27961step1 i j = -(raw27961step0 i j); unfold raw27961step1 raw27961step0; decide +kernel
      have hl : raw27961step1Labels = raw27961step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27961step1 raw27961step1Labels = mixedMoment B raw27961step2 raw27961step2Labels := by
      have ha : raw27961step2 = raw27961step1 := by apply Matrix.ext; unfold raw27961step2 raw27961step1; decide +kernel
      have hl : raw27961step1Labels = labelEmbedding10 ∘ raw27961step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27961step1 raw27961step1Labels raw27961step2Labels labelEmbedding10 hl
    _ = mixedMoment B node4992 node4992Labels := by rfl

def raw27962 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-3, 0, 3]]
def raw27962Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27962step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw27962step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw27962step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27962step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw27962step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27962step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27962 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27962 raw27962Labels = mixedMoment B node4729 node4729Labels := by
  calc
    mixedMoment B raw27962 raw27962Labels = mixedMoment B raw27962step0 raw27962step0Labels := by
      have ha : raw27962step0 = (fun i j => raw27962 (permutation682 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27962step0 raw27962; decide +kernel
      have hl : raw27962step0Labels = raw27962Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27962 raw27962Labels permutation682 permutation7
    mixedMoment B raw27962step0 raw27962step0Labels = mixedMoment B raw27962step1 raw27962step1Labels := by
      have ha : raw27962step1 = -raw27962step0 := by apply Matrix.ext; change ∀ i j, raw27962step1 i j = -(raw27962step0 i j); unfold raw27962step1 raw27962step0; decide +kernel
      have hl : raw27962step1Labels = raw27962step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27962step1 raw27962step1Labels = mixedMoment B raw27962step2 raw27962step2Labels := by
      have ha : raw27962step2 = raw27962step1 := by apply Matrix.ext; unfold raw27962step2 raw27962step1; decide +kernel
      have hl : raw27962step1Labels = labelEmbedding10 ∘ raw27962step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27962step1 raw27962step1Labels raw27962step2Labels labelEmbedding10 hl
    _ = mixedMoment B node4729 node4729Labels := by rfl

def raw27963 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw27963Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27963step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![2, -2, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw27963step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27963step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw27963step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw27963step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw27963step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27963 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27963 raw27963Labels = mixedMoment B node4817 node4817Labels := by
  calc
    mixedMoment B raw27963 raw27963Labels = mixedMoment B raw27963step0 raw27963step0Labels := by
      have hz : ∀ j, raw27963 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27963step0 = (fun i j => raw27963 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27963step0 raw27963; decide +kernel
      have hl : raw27963step0Labels = raw27963Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27963 raw27963Labels permutation346 hz
    mixedMoment B raw27963step0 raw27963step0Labels = mixedMoment B raw27963step1 raw27963step1Labels := by
      have ha : raw27963step1 = (fun i j => raw27963step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw27963step1 raw27963step0; decide +kernel
      have hl : raw27963step1Labels = raw27963step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27963step0 raw27963step0Labels permutation32 permutation6
    mixedMoment B raw27963step1 raw27963step1Labels = mixedMoment B raw27963step2 raw27963step2Labels := by
      have ha : raw27963step2 = raw27963step1 := by apply Matrix.ext; unfold raw27963step2 raw27963step1; decide +kernel
      have hl : raw27963step1Labels = labelEmbedding9 ∘ raw27963step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27963step1 raw27963step1Labels raw27963step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4817 node4817Labels := by rfl

def raw27964 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw27964Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27964step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![2, -2, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw27964step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27964step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw27964step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw27964step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw27964step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27964 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27964 raw27964Labels = mixedMoment B node5087 node5087Labels := by
  calc
    mixedMoment B raw27964 raw27964Labels = mixedMoment B raw27964step0 raw27964step0Labels := by
      have hz : ∀ j, raw27964 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27964step0 = (fun i j => raw27964 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27964step0 raw27964; decide +kernel
      have hl : raw27964step0Labels = raw27964Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27964 raw27964Labels permutation346 hz
    mixedMoment B raw27964step0 raw27964step0Labels = mixedMoment B raw27964step1 raw27964step1Labels := by
      have ha : raw27964step1 = (fun i j => raw27964step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw27964step1 raw27964step0; decide +kernel
      have hl : raw27964step1Labels = raw27964step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27964step0 raw27964step0Labels permutation32 permutation6
    mixedMoment B raw27964step1 raw27964step1Labels = mixedMoment B raw27964step2 raw27964step2Labels := by
      have ha : raw27964step2 = raw27964step1 := by apply Matrix.ext; unfold raw27964step2 raw27964step1; decide +kernel
      have hl : raw27964step1Labels = labelEmbedding9 ∘ raw27964step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27964step1 raw27964step1Labels raw27964step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5087 node5087Labels := by rfl

def raw27965 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw27965Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27965step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-3, 2, 1]]
def raw27965step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw27965step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw27965step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw27965step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw27965step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27965 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27965 raw27965Labels = mixedMoment B node5052 node5052Labels := by
  calc
    mixedMoment B raw27965 raw27965Labels = mixedMoment B raw27965step0 raw27965step0Labels := by
      have ha : raw27965step0 = (fun i j => raw27965 (permutation682 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27965step0 raw27965; decide +kernel
      have hl : raw27965step0Labels = raw27965Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27965 raw27965Labels permutation682 permutation7
    mixedMoment B raw27965step0 raw27965step0Labels = mixedMoment B raw27965step1 raw27965step1Labels := by
      have ha : raw27965step1 = -raw27965step0 := by apply Matrix.ext; change ∀ i j, raw27965step1 i j = -(raw27965step0 i j); unfold raw27965step1 raw27965step0; decide +kernel
      have hl : raw27965step1Labels = raw27965step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27965step1 raw27965step1Labels = mixedMoment B raw27965step2 raw27965step2Labels := by
      have ha : raw27965step2 = raw27965step1 := by apply Matrix.ext; unfold raw27965step2 raw27965step1; decide +kernel
      have hl : raw27965step1Labels = labelEmbedding10 ∘ raw27965step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27965step1 raw27965step1Labels raw27965step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5052 node5052Labels := by rfl

def raw27966 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![-2, -1, 3]]
def raw27966Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27966step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![2, -2, 0], ![-2, 1, 1], ![-2, -1, 3]]
def raw27966step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27966step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![0, -2, 2], ![-1, 0, 1], ![-3, 2, 1]]
def raw27966step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw27966step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw27966step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw27966step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw27966step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27966 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27966 raw27966Labels = mixedMoment B node5008 node5008Labels := by
  calc
    mixedMoment B raw27966 raw27966Labels = mixedMoment B raw27966step0 raw27966step0Labels := by
      have hz : ∀ j, raw27966 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27966step0 = (fun i j => raw27966 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27966step0 raw27966; decide +kernel
      have hl : raw27966step0Labels = raw27966Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27966 raw27966Labels permutation346 hz
    mixedMoment B raw27966step0 raw27966step0Labels = mixedMoment B raw27966step1 raw27966step1Labels := by
      have ha : raw27966step1 = (fun i j => raw27966step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27966step1 raw27966step0; decide +kernel
      have hl : raw27966step1Labels = raw27966step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27966step0 raw27966step0Labels permutation151 permutation7
    mixedMoment B raw27966step1 raw27966step1Labels = mixedMoment B raw27966step2 raw27966step2Labels := by
      have ha : raw27966step2 = -raw27966step1 := by apply Matrix.ext; change ∀ i j, raw27966step2 i j = -(raw27966step1 i j); unfold raw27966step2 raw27966step1; decide +kernel
      have hl : raw27966step2Labels = raw27966step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27966step2 raw27966step2Labels = mixedMoment B raw27966step3 raw27966step3Labels := by
      have ha : raw27966step3 = raw27966step2 := by apply Matrix.ext; unfold raw27966step3 raw27966step2; decide +kernel
      have hl : raw27966step2Labels = labelEmbedding10 ∘ raw27966step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27966step2 raw27966step2Labels raw27966step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5008 node5008Labels := by rfl

def raw27967 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-3, 0, 3]]
def raw27967Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27967step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![2, -2, 0], ![-1, 0, 1], ![-3, 0, 3]]
def raw27967step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27967step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-3, 2, 1]]
def raw27967step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw27967step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw27967step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw27967step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw27967step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27967 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27967 raw27967Labels = mixedMoment B node4747 node4747Labels := by
  calc
    mixedMoment B raw27967 raw27967Labels = mixedMoment B raw27967step0 raw27967step0Labels := by
      have hz : ∀ j, raw27967 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27967step0 = (fun i j => raw27967 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27967step0 raw27967; decide +kernel
      have hl : raw27967step0Labels = raw27967Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27967 raw27967Labels permutation346 hz
    mixedMoment B raw27967step0 raw27967step0Labels = mixedMoment B raw27967step1 raw27967step1Labels := by
      have ha : raw27967step1 = (fun i j => raw27967step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27967step1 raw27967step0; decide +kernel
      have hl : raw27967step1Labels = raw27967step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27967step0 raw27967step0Labels permutation151 permutation7
    mixedMoment B raw27967step1 raw27967step1Labels = mixedMoment B raw27967step2 raw27967step2Labels := by
      have ha : raw27967step2 = -raw27967step1 := by apply Matrix.ext; change ∀ i j, raw27967step2 i j = -(raw27967step1 i j); unfold raw27967step2 raw27967step1; decide +kernel
      have hl : raw27967step2Labels = raw27967step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27967step2 raw27967step2Labels = mixedMoment B raw27967step3 raw27967step3Labels := by
      have ha : raw27967step3 = raw27967step2 := by apply Matrix.ext; unfold raw27967step3 raw27967step2; decide +kernel
      have hl : raw27967step2Labels = labelEmbedding10 ∘ raw27967step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27967step2 raw27967step2Labels raw27967step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4747 node4747Labels := by rfl

def raw27968 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw27968Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27968step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw27968step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27968step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw27968step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw27968step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw27968step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27968 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27968 raw27968Labels = mixedMoment B node4804 node4804Labels := by
  calc
    mixedMoment B raw27968 raw27968Labels = mixedMoment B raw27968step0 raw27968step0Labels := by
      have hz : ∀ j, raw27968 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27968step0 = (fun i j => raw27968 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27968step0 raw27968; decide +kernel
      have hl : raw27968step0Labels = raw27968Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27968 raw27968Labels permutation346 hz
    mixedMoment B raw27968step0 raw27968step0Labels = mixedMoment B raw27968step1 raw27968step1Labels := by
      have ha : raw27968step1 = (fun i j => raw27968step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw27968step1 raw27968step0; decide +kernel
      have hl : raw27968step1Labels = raw27968step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27968step0 raw27968step0Labels permutation32 permutation6
    mixedMoment B raw27968step1 raw27968step1Labels = mixedMoment B raw27968step2 raw27968step2Labels := by
      have ha : raw27968step2 = raw27968step1 := by apply Matrix.ext; unfold raw27968step2 raw27968step1; decide +kernel
      have hl : raw27968step1Labels = labelEmbedding9 ∘ raw27968step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27968step1 raw27968step1Labels raw27968step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4804 node4804Labels := by rfl

def raw27969 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw27969Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27969step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw27969step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27969step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw27969step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw27969step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw27969step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27969 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27969 raw27969Labels = mixedMoment B node5075 node5075Labels := by
  calc
    mixedMoment B raw27969 raw27969Labels = mixedMoment B raw27969step0 raw27969step0Labels := by
      have hz : ∀ j, raw27969 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27969step0 = (fun i j => raw27969 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27969step0 raw27969; decide +kernel
      have hl : raw27969step0Labels = raw27969Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27969 raw27969Labels permutation346 hz
    mixedMoment B raw27969step0 raw27969step0Labels = mixedMoment B raw27969step1 raw27969step1Labels := by
      have ha : raw27969step1 = (fun i j => raw27969step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw27969step1 raw27969step0; decide +kernel
      have hl : raw27969step1Labels = raw27969step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27969step0 raw27969step0Labels permutation32 permutation6
    mixedMoment B raw27969step1 raw27969step1Labels = mixedMoment B raw27969step2 raw27969step2Labels := by
      have ha : raw27969step2 = raw27969step1 := by apply Matrix.ext; unfold raw27969step2 raw27969step1; decide +kernel
      have hl : raw27969step1Labels = labelEmbedding9 ∘ raw27969step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27969step1 raw27969step1Labels raw27969step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5075 node5075Labels := by rfl

def raw27970 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw27970Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27970step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw27970step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw27970step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw27970step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27970 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27970 raw27970Labels = mixedMoment B node5127 node5127Labels := by
  calc
    mixedMoment B raw27970 raw27970Labels = mixedMoment B raw27970step0 raw27970step0Labels := by
      have ha : raw27970step0 = (fun i j => raw27970 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw27970step0 raw27970; decide +kernel
      have hl : raw27970step0Labels = raw27970Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27970 raw27970Labels permutation152 permutation6
    mixedMoment B raw27970step0 raw27970step0Labels = mixedMoment B raw27970step1 raw27970step1Labels := by
      have ha : raw27970step1 = raw27970step0 := by apply Matrix.ext; unfold raw27970step1 raw27970step0; decide +kernel
      have hl : raw27970step0Labels = labelEmbedding9 ∘ raw27970step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27970step0 raw27970step0Labels raw27970step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5127 node5127Labels := by rfl

def raw27971 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw27971Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27971step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw27971step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27971step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw27971step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw27971step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw27971step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27971 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27971 raw27971Labels = mixedMoment B node5147 node5147Labels := by
  calc
    mixedMoment B raw27971 raw27971Labels = mixedMoment B raw27971step0 raw27971step0Labels := by
      have hz : ∀ j, raw27971 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27971step0 = (fun i j => raw27971 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27971step0 raw27971; decide +kernel
      have hl : raw27971step0Labels = raw27971Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27971 raw27971Labels permutation346 hz
    mixedMoment B raw27971step0 raw27971step0Labels = mixedMoment B raw27971step1 raw27971step1Labels := by
      have ha : raw27971step1 = (fun i j => raw27971step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw27971step1 raw27971step0; decide +kernel
      have hl : raw27971step1Labels = raw27971step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27971step0 raw27971step0Labels permutation32 permutation6
    mixedMoment B raw27971step1 raw27971step1Labels = mixedMoment B raw27971step2 raw27971step2Labels := by
      have ha : raw27971step2 = raw27971step1 := by apply Matrix.ext; unfold raw27971step2 raw27971step1; decide +kernel
      have hl : raw27971step1Labels = labelEmbedding9 ∘ raw27971step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27971step1 raw27971step1Labels raw27971step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5147 node5147Labels := by rfl

def raw27972 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw27972Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27972step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw27972step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27972step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw27972step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27972step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw27972step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27972step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw27972step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27972 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27972 raw27972Labels = mixedMoment B node2482 node2482Labels := by
  calc
    mixedMoment B raw27972 raw27972Labels = mixedMoment B raw27972step0 raw27972step0Labels := by
      have hz : ∀ j, raw27972 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27972step0 = (fun i j => raw27972 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27972step0 raw27972; decide +kernel
      have hl : raw27972step0Labels = raw27972Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27972 raw27972Labels permutation346 hz
    mixedMoment B raw27972step0 raw27972step0Labels = mixedMoment B raw27972step1 raw27972step1Labels := by
      have ha : raw27972step1 = (fun i j => raw27972step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27972step1 raw27972step0; decide +kernel
      have hl : raw27972step1Labels = raw27972step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27972step0 raw27972step0Labels permutation151 permutation7
    mixedMoment B raw27972step1 raw27972step1Labels = mixedMoment B raw27972step2 raw27972step2Labels := by
      have ha : raw27972step2 = -raw27972step1 := by apply Matrix.ext; change ∀ i j, raw27972step2 i j = -(raw27972step1 i j); unfold raw27972step2 raw27972step1; decide +kernel
      have hl : raw27972step2Labels = raw27972step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27972step2 raw27972step2Labels = mixedMoment B raw27972step3 raw27972step3Labels := by
      have ha : raw27972step3 = raw27972step2 := by apply Matrix.ext; unfold raw27972step3 raw27972step2; decide +kernel
      have hl : raw27972step2Labels = labelEmbedding1 ∘ raw27972step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27972step2 raw27972step2Labels raw27972step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2482 node2482Labels := by rfl

def raw27973 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw27973Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27973step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw27973step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27973step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw27973step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27973 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27973 raw27973Labels = mixedMoment B node2449 node2449Labels := by
  calc
    mixedMoment B raw27973 raw27973Labels = mixedMoment B raw27973step0 raw27973step0Labels := by
      have ha : raw27973step0 = (fun i j => raw27973 (permutation158 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27973step0 raw27973; decide +kernel
      have hl : raw27973step0Labels = raw27973Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27973 raw27973Labels permutation158 permutation7
    mixedMoment B raw27973step0 raw27973step0Labels = mixedMoment B raw27973step1 raw27973step1Labels := by
      have ha : raw27973step1 = raw27973step0 := by apply Matrix.ext; unfold raw27973step1 raw27973step0; decide +kernel
      have hl : raw27973step0Labels = labelEmbedding1 ∘ raw27973step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27973step0 raw27973step0Labels raw27973step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2449 node2449Labels := by rfl

def raw27974 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw27974Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27974step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 0, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw27974step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27974step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 0, 1], ![-2, -1, 3]]
def raw27974step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27974step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw27974step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27974step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw27974step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27974 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27974 raw27974Labels = mixedMoment B node2517 node2517Labels := by
  calc
    mixedMoment B raw27974 raw27974Labels = mixedMoment B raw27974step0 raw27974step0Labels := by
      have hz : ∀ j, raw27974 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27974step0 = (fun i j => raw27974 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27974step0 raw27974; decide +kernel
      have hl : raw27974step0Labels = raw27974Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27974 raw27974Labels permutation434 hz
    mixedMoment B raw27974step0 raw27974step0Labels = mixedMoment B raw27974step1 raw27974step1Labels := by
      have hz : ∀ j, raw27974step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27974step1 = (fun i j => raw27974step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27974step1 raw27974step0; decide +kernel
      have hl : raw27974step1Labels = raw27974step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27974step0 raw27974step0Labels permutation80 hz
    mixedMoment B raw27974step1 raw27974step1Labels = mixedMoment B raw27974step2 raw27974step2Labels := by
      have ha : raw27974step2 = (fun i j => raw27974step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27974step2 raw27974step1; decide +kernel
      have hl : raw27974step2Labels = raw27974step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27974step1 raw27974step1Labels permutation8 permutation7
    mixedMoment B raw27974step2 raw27974step2Labels = mixedMoment B raw27974step3 raw27974step3Labels := by
      have ha : raw27974step3 = raw27974step2 := by apply Matrix.ext; unfold raw27974step3 raw27974step2; decide +kernel
      have hl : raw27974step2Labels = labelEmbedding1 ∘ raw27974step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27974step2 raw27974step2Labels raw27974step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2517 node2517Labels := by rfl

def raw27975 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, -1, 3]]
def raw27975Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27975step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![1, -1, 0], ![-2, 1, 1], ![-2, -1, 3]]
def raw27975step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27975step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw27975step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27975step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw27975step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27975step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw27975step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27975 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27975 raw27975Labels = mixedMoment B node2385 node2385Labels := by
  calc
    mixedMoment B raw27975 raw27975Labels = mixedMoment B raw27975step0 raw27975step0Labels := by
      have hz : ∀ j, raw27975 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27975step0 = (fun i j => raw27975 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27975step0 raw27975; decide +kernel
      have hl : raw27975step0Labels = raw27975Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27975 raw27975Labels permutation346 hz
    mixedMoment B raw27975step0 raw27975step0Labels = mixedMoment B raw27975step1 raw27975step1Labels := by
      have ha : raw27975step1 = (fun i j => raw27975step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27975step1 raw27975step0; decide +kernel
      have hl : raw27975step1Labels = raw27975step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27975step0 raw27975step0Labels permutation151 permutation7
    mixedMoment B raw27975step1 raw27975step1Labels = mixedMoment B raw27975step2 raw27975step2Labels := by
      have ha : raw27975step2 = -raw27975step1 := by apply Matrix.ext; change ∀ i j, raw27975step2 i j = -(raw27975step1 i j); unfold raw27975step2 raw27975step1; decide +kernel
      have hl : raw27975step2Labels = raw27975step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27975step2 raw27975step2Labels = mixedMoment B raw27975step3 raw27975step3Labels := by
      have ha : raw27975step3 = raw27975step2 := by apply Matrix.ext; unfold raw27975step3 raw27975step2; decide +kernel
      have hl : raw27975step2Labels = labelEmbedding1 ∘ raw27975step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27975step2 raw27975step2Labels raw27975step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2385 node2385Labels := by rfl

def raw27976 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-3, 0, 3]]
def raw27976Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27976step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-3, 0, 3]]
def raw27976step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27976step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw27976step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27976step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw27976step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27976step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw27976step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27976 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27976 raw27976Labels = mixedMoment B node1914 node1914Labels := by
  calc
    mixedMoment B raw27976 raw27976Labels = mixedMoment B raw27976step0 raw27976step0Labels := by
      have hz : ∀ j, raw27976 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27976step0 = (fun i j => raw27976 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27976step0 raw27976; decide +kernel
      have hl : raw27976step0Labels = raw27976Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27976 raw27976Labels permutation346 hz
    mixedMoment B raw27976step0 raw27976step0Labels = mixedMoment B raw27976step1 raw27976step1Labels := by
      have ha : raw27976step1 = (fun i j => raw27976step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27976step1 raw27976step0; decide +kernel
      have hl : raw27976step1Labels = raw27976step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27976step0 raw27976step0Labels permutation151 permutation7
    mixedMoment B raw27976step1 raw27976step1Labels = mixedMoment B raw27976step2 raw27976step2Labels := by
      have ha : raw27976step2 = -raw27976step1 := by apply Matrix.ext; change ∀ i j, raw27976step2 i j = -(raw27976step1 i j); unfold raw27976step2 raw27976step1; decide +kernel
      have hl : raw27976step2Labels = raw27976step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27976step2 raw27976step2Labels = mixedMoment B raw27976step3 raw27976step3Labels := by
      have ha : raw27976step3 = raw27976step2 := by apply Matrix.ext; unfold raw27976step3 raw27976step2; decide +kernel
      have hl : raw27976step2Labels = labelEmbedding1 ∘ raw27976step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27976step2 raw27976step2Labels raw27976step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1914 node1914Labels := by rfl

def raw27977 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw27977Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27977step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw27977step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27977step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-3, 3, 0]]
def raw27977step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27977step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw27977step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27977step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw27977step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27977 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27977 raw27977Labels = mixedMoment B node2486 node2486Labels := by
  calc
    mixedMoment B raw27977 raw27977Labels = mixedMoment B raw27977step0 raw27977step0Labels := by
      have hz : ∀ j, raw27977 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27977step0 = (fun i j => raw27977 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27977step0 raw27977; decide +kernel
      have hl : raw27977step0Labels = raw27977Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27977 raw27977Labels permutation346 hz
    mixedMoment B raw27977step0 raw27977step0Labels = mixedMoment B raw27977step1 raw27977step1Labels := by
      have ha : raw27977step1 = (fun i j => raw27977step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27977step1 raw27977step0; decide +kernel
      have hl : raw27977step1Labels = raw27977step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27977step0 raw27977step0Labels permutation151 permutation7
    mixedMoment B raw27977step1 raw27977step1Labels = mixedMoment B raw27977step2 raw27977step2Labels := by
      have ha : raw27977step2 = -raw27977step1 := by apply Matrix.ext; change ∀ i j, raw27977step2 i j = -(raw27977step1 i j); unfold raw27977step2 raw27977step1; decide +kernel
      have hl : raw27977step2Labels = raw27977step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27977step2 raw27977step2Labels = mixedMoment B raw27977step3 raw27977step3Labels := by
      have ha : raw27977step3 = raw27977step2 := by apply Matrix.ext; unfold raw27977step3 raw27977step2; decide +kernel
      have hl : raw27977step2Labels = labelEmbedding1 ∘ raw27977step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27977step2 raw27977step2Labels raw27977step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2486 node2486Labels := by rfl

def raw27978 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw27978Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27978step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw27978step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27978step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw27978step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27978step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw27978step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27978 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27978 raw27978Labels = mixedMoment B node2450 node2450Labels := by
  calc
    mixedMoment B raw27978 raw27978Labels = mixedMoment B raw27978step0 raw27978step0Labels := by
      have ha : raw27978step0 = (fun i j => raw27978 (permutation682 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27978step0 raw27978; decide +kernel
      have hl : raw27978step0Labels = raw27978Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27978 raw27978Labels permutation682 permutation7
    mixedMoment B raw27978step0 raw27978step0Labels = mixedMoment B raw27978step1 raw27978step1Labels := by
      have ha : raw27978step1 = -raw27978step0 := by apply Matrix.ext; change ∀ i j, raw27978step1 i j = -(raw27978step0 i j); unfold raw27978step1 raw27978step0; decide +kernel
      have hl : raw27978step1Labels = raw27978step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27978step1 raw27978step1Labels = mixedMoment B raw27978step2 raw27978step2Labels := by
      have ha : raw27978step2 = raw27978step1 := by apply Matrix.ext; unfold raw27978step2 raw27978step1; decide +kernel
      have hl : raw27978step1Labels = labelEmbedding1 ∘ raw27978step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27978step1 raw27978step1Labels raw27978step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2450 node2450Labels := by rfl

def raw27979 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw27979Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27979step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw27979step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27979step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-1, 0, 1], ![-2, -1, 3]]
def raw27979step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27979step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![-1, -1, 2], ![-3, 2, 1]]
def raw27979step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27979step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw27979step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27979step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw27979step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27979 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27979 raw27979Labels = mixedMoment B node2519 node2519Labels := by
  calc
    mixedMoment B raw27979 raw27979Labels = mixedMoment B raw27979step0 raw27979step0Labels := by
      have hz : ∀ j, raw27979 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27979step0 = (fun i j => raw27979 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27979step0 raw27979; decide +kernel
      have hl : raw27979step0Labels = raw27979Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27979 raw27979Labels permutation434 hz
    mixedMoment B raw27979step0 raw27979step0Labels = mixedMoment B raw27979step1 raw27979step1Labels := by
      have hz : ∀ j, raw27979step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27979step1 = (fun i j => raw27979step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27979step1 raw27979step0; decide +kernel
      have hl : raw27979step1Labels = raw27979step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27979step0 raw27979step0Labels permutation80 hz
    mixedMoment B raw27979step1 raw27979step1Labels = mixedMoment B raw27979step2 raw27979step2Labels := by
      have ha : raw27979step2 = (fun i j => raw27979step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27979step2 raw27979step1; decide +kernel
      have hl : raw27979step2Labels = raw27979step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27979step1 raw27979step1Labels permutation31 permutation7
    mixedMoment B raw27979step2 raw27979step2Labels = mixedMoment B raw27979step3 raw27979step3Labels := by
      have ha : raw27979step3 = -raw27979step2 := by apply Matrix.ext; change ∀ i j, raw27979step3 i j = -(raw27979step2 i j); unfold raw27979step3 raw27979step2; decide +kernel
      have hl : raw27979step3Labels = raw27979step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27979step3 raw27979step3Labels = mixedMoment B raw27979step4 raw27979step4Labels := by
      have ha : raw27979step4 = raw27979step3 := by apply Matrix.ext; unfold raw27979step4 raw27979step3; decide +kernel
      have hl : raw27979step3Labels = labelEmbedding1 ∘ raw27979step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27979step3 raw27979step3Labels raw27979step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2519 node2519Labels := by rfl

def raw27980 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, -1, 3]]
def raw27980Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27980step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![1, -1, 0], ![-2, 1, 1], ![-2, -1, 3]]
def raw27980step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27980step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![0, -1, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw27980step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27980step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw27980step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27980step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw27980step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27980 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27980 raw27980Labels = mixedMoment B node2386 node2386Labels := by
  calc
    mixedMoment B raw27980 raw27980Labels = mixedMoment B raw27980step0 raw27980step0Labels := by
      have hz : ∀ j, raw27980 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27980step0 = (fun i j => raw27980 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27980step0 raw27980; decide +kernel
      have hl : raw27980step0Labels = raw27980Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27980 raw27980Labels permutation346 hz
    mixedMoment B raw27980step0 raw27980step0Labels = mixedMoment B raw27980step1 raw27980step1Labels := by
      have ha : raw27980step1 = (fun i j => raw27980step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27980step1 raw27980step0; decide +kernel
      have hl : raw27980step1Labels = raw27980step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27980step0 raw27980step0Labels permutation151 permutation7
    mixedMoment B raw27980step1 raw27980step1Labels = mixedMoment B raw27980step2 raw27980step2Labels := by
      have ha : raw27980step2 = -raw27980step1 := by apply Matrix.ext; change ∀ i j, raw27980step2 i j = -(raw27980step1 i j); unfold raw27980step2 raw27980step1; decide +kernel
      have hl : raw27980step2Labels = raw27980step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27980step2 raw27980step2Labels = mixedMoment B raw27980step3 raw27980step3Labels := by
      have ha : raw27980step3 = raw27980step2 := by apply Matrix.ext; unfold raw27980step3 raw27980step2; decide +kernel
      have hl : raw27980step2Labels = labelEmbedding1 ∘ raw27980step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27980step2 raw27980step2Labels raw27980step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2386 node2386Labels := by rfl

def raw27981 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-3, 0, 3]]
def raw27981Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27981step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![1, -1, 0], ![-1, 0, 1], ![-3, 0, 3]]
def raw27981step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27981step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw27981step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27981step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw27981step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27981step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw27981step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27981 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27981 raw27981Labels = mixedMoment B node1915 node1915Labels := by
  calc
    mixedMoment B raw27981 raw27981Labels = mixedMoment B raw27981step0 raw27981step0Labels := by
      have hz : ∀ j, raw27981 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27981step0 = (fun i j => raw27981 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27981step0 raw27981; decide +kernel
      have hl : raw27981step0Labels = raw27981Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27981 raw27981Labels permutation346 hz
    mixedMoment B raw27981step0 raw27981step0Labels = mixedMoment B raw27981step1 raw27981step1Labels := by
      have ha : raw27981step1 = (fun i j => raw27981step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27981step1 raw27981step0; decide +kernel
      have hl : raw27981step1Labels = raw27981step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27981step0 raw27981step0Labels permutation151 permutation7
    mixedMoment B raw27981step1 raw27981step1Labels = mixedMoment B raw27981step2 raw27981step2Labels := by
      have ha : raw27981step2 = -raw27981step1 := by apply Matrix.ext; change ∀ i j, raw27981step2 i j = -(raw27981step1 i j); unfold raw27981step2 raw27981step1; decide +kernel
      have hl : raw27981step2Labels = raw27981step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27981step2 raw27981step2Labels = mixedMoment B raw27981step3 raw27981step3Labels := by
      have ha : raw27981step3 = raw27981step2 := by apply Matrix.ext; unfold raw27981step3 raw27981step2; decide +kernel
      have hl : raw27981step2Labels = labelEmbedding1 ∘ raw27981step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27981step2 raw27981step2Labels raw27981step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1915 node1915Labels := by rfl

def raw27982 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw27982Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27982step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-3, 3, 0]]
def raw27982step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27982step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw27982step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27982step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw27982step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27982 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27982 raw27982Labels = mixedMoment B node2471 node2471Labels := by
  calc
    mixedMoment B raw27982 raw27982Labels = mixedMoment B raw27982step0 raw27982step0Labels := by
      have ha : raw27982step0 = (fun i j => raw27982 (permutation682 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27982step0 raw27982; decide +kernel
      have hl : raw27982step0Labels = raw27982Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27982 raw27982Labels permutation682 permutation7
    mixedMoment B raw27982step0 raw27982step0Labels = mixedMoment B raw27982step1 raw27982step1Labels := by
      have ha : raw27982step1 = -raw27982step0 := by apply Matrix.ext; change ∀ i j, raw27982step1 i j = -(raw27982step0 i j); unfold raw27982step1 raw27982step0; decide +kernel
      have hl : raw27982step1Labels = raw27982step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27982step1 raw27982step1Labels = mixedMoment B raw27982step2 raw27982step2Labels := by
      have ha : raw27982step2 = raw27982step1 := by apply Matrix.ext; unfold raw27982step2 raw27982step1; decide +kernel
      have hl : raw27982step1Labels = labelEmbedding1 ∘ raw27982step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27982step1 raw27982step1Labels raw27982step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2471 node2471Labels := by rfl

def raw27983 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw27983Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27983step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 2, 1]]
def raw27983step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27983step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw27983step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27983step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw27983step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27983 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27983 raw27983Labels = mixedMoment B node2470 node2470Labels := by
  calc
    mixedMoment B raw27983 raw27983Labels = mixedMoment B raw27983step0 raw27983step0Labels := by
      have ha : raw27983step0 = (fun i j => raw27983 (permutation682 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27983step0 raw27983; decide +kernel
      have hl : raw27983step0Labels = raw27983Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27983 raw27983Labels permutation682 permutation7
    mixedMoment B raw27983step0 raw27983step0Labels = mixedMoment B raw27983step1 raw27983step1Labels := by
      have ha : raw27983step1 = -raw27983step0 := by apply Matrix.ext; change ∀ i j, raw27983step1 i j = -(raw27983step0 i j); unfold raw27983step1 raw27983step0; decide +kernel
      have hl : raw27983step1Labels = raw27983step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27983step1 raw27983step1Labels = mixedMoment B raw27983step2 raw27983step2Labels := by
      have ha : raw27983step2 = raw27983step1 := by apply Matrix.ext; unfold raw27983step2 raw27983step1; decide +kernel
      have hl : raw27983step1Labels = labelEmbedding1 ∘ raw27983step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27983step1 raw27983step1Labels raw27983step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2470 node2470Labels := by rfl

def raw27984 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw27984Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27984step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw27984step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27984step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw27984step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27984step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27984step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27984step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27984step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27984 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27984 raw27984Labels = mixedMoment B node2485 node2485Labels := by
  calc
    mixedMoment B raw27984 raw27984Labels = mixedMoment B raw27984step0 raw27984step0Labels := by
      have hz : ∀ j, raw27984 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27984step0 = (fun i j => raw27984 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27984step0 raw27984; decide +kernel
      have hl : raw27984step0Labels = raw27984Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27984 raw27984Labels permutation434 hz
    mixedMoment B raw27984step0 raw27984step0Labels = mixedMoment B raw27984step1 raw27984step1Labels := by
      have ha : raw27984step1 = (fun i j => raw27984step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27984step1 raw27984step0; decide +kernel
      have hl : raw27984step1Labels = raw27984step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27984step0 raw27984step0Labels permutation151 permutation7
    mixedMoment B raw27984step1 raw27984step1Labels = mixedMoment B raw27984step2 raw27984step2Labels := by
      have ha : raw27984step2 = -raw27984step1 := by apply Matrix.ext; change ∀ i j, raw27984step2 i j = -(raw27984step1 i j); unfold raw27984step2 raw27984step1; decide +kernel
      have hl : raw27984step2Labels = raw27984step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27984step2 raw27984step2Labels = mixedMoment B raw27984step3 raw27984step3Labels := by
      have ha : raw27984step3 = raw27984step2 := by apply Matrix.ext; unfold raw27984step3 raw27984step2; decide +kernel
      have hl : raw27984step2Labels = labelEmbedding1 ∘ raw27984step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27984step2 raw27984step2Labels raw27984step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2485 node2485Labels := by rfl

def raw27985 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, -1, 3]]
def raw27985Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27985step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw27985step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27985step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27985step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27985step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27985step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27985 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27985 raw27985Labels = mixedMoment B node2378 node2378Labels := by
  calc
    mixedMoment B raw27985 raw27985Labels = mixedMoment B raw27985step0 raw27985step0Labels := by
      have ha : raw27985step0 = (fun i j => raw27985 (permutation682 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27985step0 raw27985; decide +kernel
      have hl : raw27985step0Labels = raw27985Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27985 raw27985Labels permutation682 permutation7
    mixedMoment B raw27985step0 raw27985step0Labels = mixedMoment B raw27985step1 raw27985step1Labels := by
      have ha : raw27985step1 = -raw27985step0 := by apply Matrix.ext; change ∀ i j, raw27985step1 i j = -(raw27985step0 i j); unfold raw27985step1 raw27985step0; decide +kernel
      have hl : raw27985step1Labels = raw27985step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27985step1 raw27985step1Labels = mixedMoment B raw27985step2 raw27985step2Labels := by
      have ha : raw27985step2 = raw27985step1 := by apply Matrix.ext; unfold raw27985step2 raw27985step1; decide +kernel
      have hl : raw27985step1Labels = labelEmbedding1 ∘ raw27985step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27985step1 raw27985step1Labels raw27985step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2378 node2378Labels := by rfl

def raw27986 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-3, 0, 3]]
def raw27986Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27986step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw27986step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27986step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27986step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27986step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27986step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27986 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27986 raw27986Labels = mixedMoment B node1898 node1898Labels := by
  calc
    mixedMoment B raw27986 raw27986Labels = mixedMoment B raw27986step0 raw27986step0Labels := by
      have ha : raw27986step0 = (fun i j => raw27986 (permutation682 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27986step0 raw27986; decide +kernel
      have hl : raw27986step0Labels = raw27986Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27986 raw27986Labels permutation682 permutation7
    mixedMoment B raw27986step0 raw27986step0Labels = mixedMoment B raw27986step1 raw27986step1Labels := by
      have ha : raw27986step1 = -raw27986step0 := by apply Matrix.ext; change ∀ i j, raw27986step1 i j = -(raw27986step0 i j); unfold raw27986step1 raw27986step0; decide +kernel
      have hl : raw27986step1Labels = raw27986step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27986step1 raw27986step1Labels = mixedMoment B raw27986step2 raw27986step2Labels := by
      have ha : raw27986step2 = raw27986step1 := by apply Matrix.ext; unfold raw27986step2 raw27986step1; decide +kernel
      have hl : raw27986step1Labels = labelEmbedding1 ∘ raw27986step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27986step1 raw27986step1Labels raw27986step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1898 node1898Labels := by rfl

def raw27987 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw27987Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27987step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![2, -2, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw27987step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27987step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-3, 3, 0]]
def raw27987step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27987step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw27987step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27987step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw27987step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27987 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27987 raw27987Labels = mixedMoment B node2497 node2497Labels := by
  calc
    mixedMoment B raw27987 raw27987Labels = mixedMoment B raw27987step0 raw27987step0Labels := by
      have hz : ∀ j, raw27987 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27987step0 = (fun i j => raw27987 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27987step0 raw27987; decide +kernel
      have hl : raw27987step0Labels = raw27987Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27987 raw27987Labels permutation346 hz
    mixedMoment B raw27987step0 raw27987step0Labels = mixedMoment B raw27987step1 raw27987step1Labels := by
      have ha : raw27987step1 = (fun i j => raw27987step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27987step1 raw27987step0; decide +kernel
      have hl : raw27987step1Labels = raw27987step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27987step0 raw27987step0Labels permutation151 permutation7
    mixedMoment B raw27987step1 raw27987step1Labels = mixedMoment B raw27987step2 raw27987step2Labels := by
      have ha : raw27987step2 = -raw27987step1 := by apply Matrix.ext; change ∀ i j, raw27987step2 i j = -(raw27987step1 i j); unfold raw27987step2 raw27987step1; decide +kernel
      have hl : raw27987step2Labels = raw27987step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27987step2 raw27987step2Labels = mixedMoment B raw27987step3 raw27987step3Labels := by
      have ha : raw27987step3 = raw27987step2 := by apply Matrix.ext; unfold raw27987step3 raw27987step2; decide +kernel
      have hl : raw27987step2Labels = labelEmbedding1 ∘ raw27987step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27987step2 raw27987step2Labels raw27987step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2497 node2497Labels := by rfl

def raw27988 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw27988Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27988step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![2, -2, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw27988step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27988step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-3, 2, 1]]
def raw27988step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27988step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw27988step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27988step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw27988step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27988 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27988 raw27988Labels = mixedMoment B node2495 node2495Labels := by
  calc
    mixedMoment B raw27988 raw27988Labels = mixedMoment B raw27988step0 raw27988step0Labels := by
      have hz : ∀ j, raw27988 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27988step0 = (fun i j => raw27988 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27988step0 raw27988; decide +kernel
      have hl : raw27988step0Labels = raw27988Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27988 raw27988Labels permutation346 hz
    mixedMoment B raw27988step0 raw27988step0Labels = mixedMoment B raw27988step1 raw27988step1Labels := by
      have ha : raw27988step1 = (fun i j => raw27988step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27988step1 raw27988step0; decide +kernel
      have hl : raw27988step1Labels = raw27988step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27988step0 raw27988step0Labels permutation151 permutation7
    mixedMoment B raw27988step1 raw27988step1Labels = mixedMoment B raw27988step2 raw27988step2Labels := by
      have ha : raw27988step2 = -raw27988step1 := by apply Matrix.ext; change ∀ i j, raw27988step2 i j = -(raw27988step1 i j); unfold raw27988step2 raw27988step1; decide +kernel
      have hl : raw27988step2Labels = raw27988step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27988step2 raw27988step2Labels = mixedMoment B raw27988step3 raw27988step3Labels := by
      have ha : raw27988step3 = raw27988step2 := by apply Matrix.ext; unfold raw27988step3 raw27988step2; decide +kernel
      have hl : raw27988step2Labels = labelEmbedding1 ∘ raw27988step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27988step2 raw27988step2Labels raw27988step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2495 node2495Labels := by rfl

def raw27989 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw27989Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27989step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-3, 2, 1]]
def raw27989step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27989step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw27989step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27989step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw27989step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27989 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27989 raw27989Labels = mixedMoment B node2454 node2454Labels := by
  calc
    mixedMoment B raw27989 raw27989Labels = mixedMoment B raw27989step0 raw27989step0Labels := by
      have ha : raw27989step0 = (fun i j => raw27989 (permutation682 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27989step0 raw27989; decide +kernel
      have hl : raw27989step0Labels = raw27989Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27989 raw27989Labels permutation682 permutation7
    mixedMoment B raw27989step0 raw27989step0Labels = mixedMoment B raw27989step1 raw27989step1Labels := by
      have ha : raw27989step1 = -raw27989step0 := by apply Matrix.ext; change ∀ i j, raw27989step1 i j = -(raw27989step0 i j); unfold raw27989step1 raw27989step0; decide +kernel
      have hl : raw27989step1Labels = raw27989step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27989step1 raw27989step1Labels = mixedMoment B raw27989step2 raw27989step2Labels := by
      have ha : raw27989step2 = raw27989step1 := by apply Matrix.ext; unfold raw27989step2 raw27989step1; decide +kernel
      have hl : raw27989step1Labels = labelEmbedding1 ∘ raw27989step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27989step1 raw27989step1Labels raw27989step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2454 node2454Labels := by rfl

def raw27990 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![-2, -1, 3]]
def raw27990Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27990step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![2, -2, 0], ![-2, 1, 1], ![-2, -1, 3]]
def raw27990step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27990step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![0, -2, 2], ![-1, 0, 1], ![-3, 2, 1]]
def raw27990step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27990step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw27990step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27990step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw27990step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27990 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27990 raw27990Labels = mixedMoment B node2393 node2393Labels := by
  calc
    mixedMoment B raw27990 raw27990Labels = mixedMoment B raw27990step0 raw27990step0Labels := by
      have hz : ∀ j, raw27990 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27990step0 = (fun i j => raw27990 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27990step0 raw27990; decide +kernel
      have hl : raw27990step0Labels = raw27990Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27990 raw27990Labels permutation346 hz
    mixedMoment B raw27990step0 raw27990step0Labels = mixedMoment B raw27990step1 raw27990step1Labels := by
      have ha : raw27990step1 = (fun i j => raw27990step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27990step1 raw27990step0; decide +kernel
      have hl : raw27990step1Labels = raw27990step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27990step0 raw27990step0Labels permutation151 permutation7
    mixedMoment B raw27990step1 raw27990step1Labels = mixedMoment B raw27990step2 raw27990step2Labels := by
      have ha : raw27990step2 = -raw27990step1 := by apply Matrix.ext; change ∀ i j, raw27990step2 i j = -(raw27990step1 i j); unfold raw27990step2 raw27990step1; decide +kernel
      have hl : raw27990step2Labels = raw27990step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27990step2 raw27990step2Labels = mixedMoment B raw27990step3 raw27990step3Labels := by
      have ha : raw27990step3 = raw27990step2 := by apply Matrix.ext; unfold raw27990step3 raw27990step2; decide +kernel
      have hl : raw27990step2Labels = labelEmbedding1 ∘ raw27990step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27990step2 raw27990step2Labels raw27990step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2393 node2393Labels := by rfl

def raw27991 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-3, 0, 3]]
def raw27991Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27991step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![2, -2, 0], ![-1, 0, 1], ![-3, 0, 3]]
def raw27991step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27991step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-3, 2, 1]]
def raw27991step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27991step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw27991step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27991step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw27991step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27991 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27991 raw27991Labels = mixedMoment B node1926 node1926Labels := by
  calc
    mixedMoment B raw27991 raw27991Labels = mixedMoment B raw27991step0 raw27991step0Labels := by
      have hz : ∀ j, raw27991 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27991step0 = (fun i j => raw27991 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27991step0 raw27991; decide +kernel
      have hl : raw27991step0Labels = raw27991Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27991 raw27991Labels permutation346 hz
    mixedMoment B raw27991step0 raw27991step0Labels = mixedMoment B raw27991step1 raw27991step1Labels := by
      have ha : raw27991step1 = (fun i j => raw27991step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27991step1 raw27991step0; decide +kernel
      have hl : raw27991step1Labels = raw27991step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27991step0 raw27991step0Labels permutation151 permutation7
    mixedMoment B raw27991step1 raw27991step1Labels = mixedMoment B raw27991step2 raw27991step2Labels := by
      have ha : raw27991step2 = -raw27991step1 := by apply Matrix.ext; change ∀ i j, raw27991step2 i j = -(raw27991step1 i j); unfold raw27991step2 raw27991step1; decide +kernel
      have hl : raw27991step2Labels = raw27991step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27991step2 raw27991step2Labels = mixedMoment B raw27991step3 raw27991step3Labels := by
      have ha : raw27991step3 = raw27991step2 := by apply Matrix.ext; unfold raw27991step3 raw27991step2; decide +kernel
      have hl : raw27991step2Labels = labelEmbedding1 ∘ raw27991step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27991step2 raw27991step2Labels raw27991step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1926 node1926Labels := by rfl

def raw27992 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw27992Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27992step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw27992step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27992step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-3, 3, 0]]
def raw27992step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27992step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw27992step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27992step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw27992step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27992 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27992 raw27992Labels = mixedMoment B node2574 node2574Labels := by
  calc
    mixedMoment B raw27992 raw27992Labels = mixedMoment B raw27992step0 raw27992step0Labels := by
      have hz : ∀ j, raw27992 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27992step0 = (fun i j => raw27992 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27992step0 raw27992; decide +kernel
      have hl : raw27992step0Labels = raw27992Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27992 raw27992Labels permutation346 hz
    mixedMoment B raw27992step0 raw27992step0Labels = mixedMoment B raw27992step1 raw27992step1Labels := by
      have ha : raw27992step1 = (fun i j => raw27992step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27992step1 raw27992step0; decide +kernel
      have hl : raw27992step1Labels = raw27992step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27992step0 raw27992step0Labels permutation151 permutation7
    mixedMoment B raw27992step1 raw27992step1Labels = mixedMoment B raw27992step2 raw27992step2Labels := by
      have ha : raw27992step2 = -raw27992step1 := by apply Matrix.ext; change ∀ i j, raw27992step2 i j = -(raw27992step1 i j); unfold raw27992step2 raw27992step1; decide +kernel
      have hl : raw27992step2Labels = raw27992step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27992step2 raw27992step2Labels = mixedMoment B raw27992step3 raw27992step3Labels := by
      have ha : raw27992step3 = raw27992step2 := by apply Matrix.ext; unfold raw27992step3 raw27992step2; decide +kernel
      have hl : raw27992step2Labels = labelEmbedding1 ∘ raw27992step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27992step2 raw27992step2Labels raw27992step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2574 node2574Labels := by rfl

def raw27993 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw27993Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27993step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw27993step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27993step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-3, 2, 1]]
def raw27993step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27993step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw27993step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27993step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw27993step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27993 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27993 raw27993Labels = mixedMoment B node2572 node2572Labels := by
  calc
    mixedMoment B raw27993 raw27993Labels = mixedMoment B raw27993step0 raw27993step0Labels := by
      have hz : ∀ j, raw27993 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27993step0 = (fun i j => raw27993 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27993step0 raw27993; decide +kernel
      have hl : raw27993step0Labels = raw27993Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27993 raw27993Labels permutation346 hz
    mixedMoment B raw27993step0 raw27993step0Labels = mixedMoment B raw27993step1 raw27993step1Labels := by
      have ha : raw27993step1 = (fun i j => raw27993step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27993step1 raw27993step0; decide +kernel
      have hl : raw27993step1Labels = raw27993step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27993step0 raw27993step0Labels permutation151 permutation7
    mixedMoment B raw27993step1 raw27993step1Labels = mixedMoment B raw27993step2 raw27993step2Labels := by
      have ha : raw27993step2 = -raw27993step1 := by apply Matrix.ext; change ∀ i j, raw27993step2 i j = -(raw27993step1 i j); unfold raw27993step2 raw27993step1; decide +kernel
      have hl : raw27993step2Labels = raw27993step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27993step2 raw27993step2Labels = mixedMoment B raw27993step3 raw27993step3Labels := by
      have ha : raw27993step3 = raw27993step2 := by apply Matrix.ext; unfold raw27993step3 raw27993step2; decide +kernel
      have hl : raw27993step2Labels = labelEmbedding1 ∘ raw27993step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27993step2 raw27993step2Labels raw27993step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2572 node2572Labels := by rfl

def raw27994 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw27994Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27994step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw27994step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27994step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27994step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27994step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27994step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27994 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27994 raw27994Labels = mixedMoment B node2543 node2543Labels := by
  calc
    mixedMoment B raw27994 raw27994Labels = mixedMoment B raw27994step0 raw27994step0Labels := by
      have ha : raw27994step0 = (fun i j => raw27994 (permutation682 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27994step0 raw27994; decide +kernel
      have hl : raw27994step0Labels = raw27994Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27994 raw27994Labels permutation682 permutation7
    mixedMoment B raw27994step0 raw27994step0Labels = mixedMoment B raw27994step1 raw27994step1Labels := by
      have ha : raw27994step1 = -raw27994step0 := by apply Matrix.ext; change ∀ i j, raw27994step1 i j = -(raw27994step0 i j); unfold raw27994step1 raw27994step0; decide +kernel
      have hl : raw27994step1Labels = raw27994step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27994step1 raw27994step1Labels = mixedMoment B raw27994step2 raw27994step2Labels := by
      have ha : raw27994step2 = raw27994step1 := by apply Matrix.ext; unfold raw27994step2 raw27994step1; decide +kernel
      have hl : raw27994step1Labels = labelEmbedding1 ∘ raw27994step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27994step1 raw27994step1Labels raw27994step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2543 node2543Labels := by rfl

def raw27995 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw27995Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27995step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw27995step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27995step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 3, 0]]
def raw27995step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27995step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw27995step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27995step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw27995step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27995 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27995 raw27995Labels = mixedMoment B node2941 node2941Labels := by
  calc
    mixedMoment B raw27995 raw27995Labels = mixedMoment B raw27995step0 raw27995step0Labels := by
      have hz : ∀ j, raw27995 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27995step0 = (fun i j => raw27995 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27995step0 raw27995; decide +kernel
      have hl : raw27995step0Labels = raw27995Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27995 raw27995Labels permutation346 hz
    mixedMoment B raw27995step0 raw27995step0Labels = mixedMoment B raw27995step1 raw27995step1Labels := by
      have ha : raw27995step1 = (fun i j => raw27995step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27995step1 raw27995step0; decide +kernel
      have hl : raw27995step1Labels = raw27995step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27995step0 raw27995step0Labels permutation151 permutation7
    mixedMoment B raw27995step1 raw27995step1Labels = mixedMoment B raw27995step2 raw27995step2Labels := by
      have ha : raw27995step2 = -raw27995step1 := by apply Matrix.ext; change ∀ i j, raw27995step2 i j = -(raw27995step1 i j); unfold raw27995step2 raw27995step1; decide +kernel
      have hl : raw27995step2Labels = raw27995step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27995step2 raw27995step2Labels = mixedMoment B raw27995step3 raw27995step3Labels := by
      have ha : raw27995step3 = raw27995step2 := by apply Matrix.ext; unfold raw27995step3 raw27995step2; decide +kernel
      have hl : raw27995step2Labels = labelEmbedding1 ∘ raw27995step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27995step2 raw27995step2Labels raw27995step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2941 node2941Labels := by rfl

def raw27996 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw27996Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27996step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw27996step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27996step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-3, 2, 1]]
def raw27996step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27996step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw27996step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27996step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw27996step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27996 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27996 raw27996Labels = mixedMoment B node2939 node2939Labels := by
  calc
    mixedMoment B raw27996 raw27996Labels = mixedMoment B raw27996step0 raw27996step0Labels := by
      have hz : ∀ j, raw27996 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27996step0 = (fun i j => raw27996 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27996step0 raw27996; decide +kernel
      have hl : raw27996step0Labels = raw27996Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27996 raw27996Labels permutation346 hz
    mixedMoment B raw27996step0 raw27996step0Labels = mixedMoment B raw27996step1 raw27996step1Labels := by
      have ha : raw27996step1 = (fun i j => raw27996step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27996step1 raw27996step0; decide +kernel
      have hl : raw27996step1Labels = raw27996step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27996step0 raw27996step0Labels permutation151 permutation7
    mixedMoment B raw27996step1 raw27996step1Labels = mixedMoment B raw27996step2 raw27996step2Labels := by
      have ha : raw27996step2 = -raw27996step1 := by apply Matrix.ext; change ∀ i j, raw27996step2 i j = -(raw27996step1 i j); unfold raw27996step2 raw27996step1; decide +kernel
      have hl : raw27996step2Labels = raw27996step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27996step2 raw27996step2Labels = mixedMoment B raw27996step3 raw27996step3Labels := by
      have ha : raw27996step3 = raw27996step2 := by apply Matrix.ext; unfold raw27996step3 raw27996step2; decide +kernel
      have hl : raw27996step2Labels = labelEmbedding1 ∘ raw27996step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27996step2 raw27996step2Labels raw27996step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2939 node2939Labels := by rfl

def raw27997 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw27997Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27997step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27997step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27997step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27997step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27997 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27997 raw27997Labels = mixedMoment B node2914 node2914Labels := by
  calc
    mixedMoment B raw27997 raw27997Labels = mixedMoment B raw27997step0 raw27997step0Labels := by
      have ha : raw27997step0 = (fun i j => raw27997 (permutation158 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27997step0 raw27997; decide +kernel
      have hl : raw27997step0Labels = raw27997Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27997 raw27997Labels permutation158 permutation7
    mixedMoment B raw27997step0 raw27997step0Labels = mixedMoment B raw27997step1 raw27997step1Labels := by
      have ha : raw27997step1 = raw27997step0 := by apply Matrix.ext; unfold raw27997step1 raw27997step0; decide +kernel
      have hl : raw27997step0Labels = labelEmbedding1 ∘ raw27997step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27997step0 raw27997step0Labels raw27997step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2914 node2914Labels := by rfl

def raw27998 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw27998Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27998step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw27998step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27998step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 0, 1], ![-1, -2, 3]]
def raw27998step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27998step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![3, -2, -1]]
def raw27998step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27998step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![3, -2, -1]]
def raw27998step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27998 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27998 raw27998Labels = mixedMoment B node2965 node2965Labels := by
  calc
    mixedMoment B raw27998 raw27998Labels = mixedMoment B raw27998step0 raw27998step0Labels := by
      have hz : ∀ j, raw27998 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27998step0 = (fun i j => raw27998 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27998step0 raw27998; decide +kernel
      have hl : raw27998step0Labels = raw27998Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27998 raw27998Labels permutation434 hz
    mixedMoment B raw27998step0 raw27998step0Labels = mixedMoment B raw27998step1 raw27998step1Labels := by
      have hz : ∀ j, raw27998step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27998step1 = (fun i j => raw27998step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27998step1 raw27998step0; decide +kernel
      have hl : raw27998step1Labels = raw27998step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27998step0 raw27998step0Labels permutation80 hz
    mixedMoment B raw27998step1 raw27998step1Labels = mixedMoment B raw27998step2 raw27998step2Labels := by
      have ha : raw27998step2 = (fun i j => raw27998step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27998step2 raw27998step1; decide +kernel
      have hl : raw27998step2Labels = raw27998step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27998step1 raw27998step1Labels permutation8 permutation7
    mixedMoment B raw27998step2 raw27998step2Labels = mixedMoment B raw27998step3 raw27998step3Labels := by
      have ha : raw27998step3 = raw27998step2 := by apply Matrix.ext; unfold raw27998step3 raw27998step2; decide +kernel
      have hl : raw27998step2Labels = labelEmbedding1 ∘ raw27998step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27998step2 raw27998step2Labels raw27998step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2965 node2965Labels := by rfl

def raw27999 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw27999Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27999step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw27999step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27999step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw27999step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27999step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27999step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27999step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27999step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27999 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27999 raw27999Labels = mixedMoment B node2865 node2865Labels := by
  calc
    mixedMoment B raw27999 raw27999Labels = mixedMoment B raw27999step0 raw27999step0Labels := by
      have hz : ∀ j, raw27999 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27999step0 = (fun i j => raw27999 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27999step0 raw27999; decide +kernel
      have hl : raw27999step0Labels = raw27999Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27999 raw27999Labels permutation346 hz
    mixedMoment B raw27999step0 raw27999step0Labels = mixedMoment B raw27999step1 raw27999step1Labels := by
      have ha : raw27999step1 = (fun i j => raw27999step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27999step1 raw27999step0; decide +kernel
      have hl : raw27999step1Labels = raw27999step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27999step0 raw27999step0Labels permutation151 permutation7
    mixedMoment B raw27999step1 raw27999step1Labels = mixedMoment B raw27999step2 raw27999step2Labels := by
      have ha : raw27999step2 = -raw27999step1 := by apply Matrix.ext; change ∀ i j, raw27999step2 i j = -(raw27999step1 i j); unfold raw27999step2 raw27999step1; decide +kernel
      have hl : raw27999step2Labels = raw27999step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27999step2 raw27999step2Labels = mixedMoment B raw27999step3 raw27999step3Labels := by
      have ha : raw27999step3 = raw27999step2 := by apply Matrix.ext; unfold raw27999step3 raw27999step2; decide +kernel
      have hl : raw27999step2Labels = labelEmbedding1 ∘ raw27999step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27999step2 raw27999step2Labels raw27999step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2865 node2865Labels := by rfl

def raw28000 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw28000Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28000step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2], ![-3, 2, 1]]
def raw28000step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28000step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def raw28000step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28000step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def raw28000step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28000 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28000 raw28000Labels = mixedMoment B node4707 node4707Labels := by
  calc
    mixedMoment B raw28000 raw28000Labels = mixedMoment B raw28000step0 raw28000step0Labels := by
      have ha : raw28000step0 = (fun i j => raw28000 (permutation646 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28000step0 raw28000; decide +kernel
      have hl : raw28000step0Labels = raw28000Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28000 raw28000Labels permutation646 permutation3
    mixedMoment B raw28000step0 raw28000step0Labels = mixedMoment B raw28000step1 raw28000step1Labels := by
      have ha : raw28000step1 = -raw28000step0 := by apply Matrix.ext; change ∀ i j, raw28000step1 i j = -(raw28000step0 i j); unfold raw28000step1 raw28000step0; decide +kernel
      have hl : raw28000step1Labels = raw28000step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28000step1 raw28000step1Labels = mixedMoment B raw28000step2 raw28000step2Labels := by
      have ha : raw28000step2 = raw28000step1 := by apply Matrix.ext; unfold raw28000step2 raw28000step1; decide +kernel
      have hl : raw28000step1Labels = labelEmbedding6 ∘ raw28000step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28000step1 raw28000step1Labels raw28000step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4707 node4707Labels := by rfl

def raw28001 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![-1, 2, -1], ![1, 0, -1], ![3, -3, 0]]
def raw28001Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28001step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw28001step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28001step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw28001step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28001step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw28001step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28001 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28001 raw28001Labels = mixedMoment B node4713 node4713Labels := by
  calc
    mixedMoment B raw28001 raw28001Labels = mixedMoment B raw28001step0 raw28001step0Labels := by
      have ha : raw28001step0 = (fun i j => raw28001 (permutation644 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28001step0 raw28001; decide +kernel
      have hl : raw28001step0Labels = raw28001Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28001 raw28001Labels permutation644 permutation3
    mixedMoment B raw28001step0 raw28001step0Labels = mixedMoment B raw28001step1 raw28001step1Labels := by
      have ha : raw28001step1 = -raw28001step0 := by apply Matrix.ext; change ∀ i j, raw28001step1 i j = -(raw28001step0 i j); unfold raw28001step1 raw28001step0; decide +kernel
      have hl : raw28001step1Labels = raw28001step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28001step1 raw28001step1Labels = mixedMoment B raw28001step2 raw28001step2Labels := by
      have ha : raw28001step2 = raw28001step1 := by apply Matrix.ext; unfold raw28001step2 raw28001step1; decide +kernel
      have hl : raw28001step1Labels = labelEmbedding6 ∘ raw28001step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28001step1 raw28001step1Labels raw28001step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4713 node4713Labels := by rfl

def raw28002 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw28002Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28002step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw28002step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28002step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2], ![-3, 2, 1]]
def raw28002step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28002step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw28002step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28002step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw28002step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28002 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28002 raw28002Labels = mixedMoment B node4770 node4770Labels := by
  calc
    mixedMoment B raw28002 raw28002Labels = mixedMoment B raw28002step0 raw28002step0Labels := by
      have hz : ∀ j, raw28002 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28002step0 = (fun i j => raw28002 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28002step0 raw28002; decide +kernel
      have hl : raw28002step0Labels = raw28002Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28002 raw28002Labels permutation346 hz
    mixedMoment B raw28002step0 raw28002step0Labels = mixedMoment B raw28002step1 raw28002step1Labels := by
      have ha : raw28002step1 = (fun i j => raw28002step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28002step1 raw28002step0; decide +kernel
      have hl : raw28002step1Labels = raw28002step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28002step0 raw28002step0Labels permutation145 permutation3
    mixedMoment B raw28002step1 raw28002step1Labels = mixedMoment B raw28002step2 raw28002step2Labels := by
      have ha : raw28002step2 = -raw28002step1 := by apply Matrix.ext; change ∀ i j, raw28002step2 i j = -(raw28002step1 i j); unfold raw28002step2 raw28002step1; decide +kernel
      have hl : raw28002step2Labels = raw28002step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28002step2 raw28002step2Labels = mixedMoment B raw28002step3 raw28002step3Labels := by
      have ha : raw28002step3 = raw28002step2 := by apply Matrix.ext; unfold raw28002step3 raw28002step2; decide +kernel
      have hl : raw28002step2Labels = labelEmbedding6 ∘ raw28002step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28002step2 raw28002step2Labels raw28002step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4770 node4770Labels := by rfl

def raw28003 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw28003Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28003step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw28003step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28003step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw28003step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28003step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw28003step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28003 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28003 raw28003Labels = mixedMoment B node4764 node4764Labels := by
  calc
    mixedMoment B raw28003 raw28003Labels = mixedMoment B raw28003step0 raw28003step0Labels := by
      have ha : raw28003step0 = (fun i j => raw28003 (permutation662 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28003step0 raw28003; decide +kernel
      have hl : raw28003step0Labels = raw28003Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28003 raw28003Labels permutation662 permutation3
    mixedMoment B raw28003step0 raw28003step0Labels = mixedMoment B raw28003step1 raw28003step1Labels := by
      have ha : raw28003step1 = -raw28003step0 := by apply Matrix.ext; change ∀ i j, raw28003step1 i j = -(raw28003step0 i j); unfold raw28003step1 raw28003step0; decide +kernel
      have hl : raw28003step1Labels = raw28003step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28003step1 raw28003step1Labels = mixedMoment B raw28003step2 raw28003step2Labels := by
      have ha : raw28003step2 = raw28003step1 := by apply Matrix.ext; unfold raw28003step2 raw28003step1; decide +kernel
      have hl : raw28003step1Labels = labelEmbedding6 ∘ raw28003step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28003step1 raw28003step1Labels raw28003step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4764 node4764Labels := by rfl

def raw28004 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![3, -3, 0]]
def raw28004Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28004step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 1, -1], ![2, -1, -1], ![3, -3, 0]]
def raw28004step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28004step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -1, -1], ![0, -1, 1], ![-2, 0, 2], ![-3, 2, 1]]
def raw28004step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28004step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def raw28004step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28004step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def raw28004step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28004 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28004 raw28004Labels = mixedMoment B node4638 node4638Labels := by
  calc
    mixedMoment B raw28004 raw28004Labels = mixedMoment B raw28004step0 raw28004step0Labels := by
      have hz : ∀ j, raw28004 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28004step0 = (fun i j => raw28004 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28004step0 raw28004; decide +kernel
      have hl : raw28004step0Labels = raw28004Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28004 raw28004Labels permutation346 hz
    mixedMoment B raw28004step0 raw28004step0Labels = mixedMoment B raw28004step1 raw28004step1Labels := by
      have ha : raw28004step1 = (fun i j => raw28004step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28004step1 raw28004step0; decide +kernel
      have hl : raw28004step1Labels = raw28004step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28004step0 raw28004step0Labels permutation151 permutation3
    mixedMoment B raw28004step1 raw28004step1Labels = mixedMoment B raw28004step2 raw28004step2Labels := by
      have ha : raw28004step2 = -raw28004step1 := by apply Matrix.ext; change ∀ i j, raw28004step2 i j = -(raw28004step1 i j); unfold raw28004step2 raw28004step1; decide +kernel
      have hl : raw28004step2Labels = raw28004step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28004step2 raw28004step2Labels = mixedMoment B raw28004step3 raw28004step3Labels := by
      have ha : raw28004step3 = raw28004step2 := by apply Matrix.ext; unfold raw28004step3 raw28004step2; decide +kernel
      have hl : raw28004step2Labels = labelEmbedding6 ∘ raw28004step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28004step2 raw28004step2Labels raw28004step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4638 node4638Labels := by rfl

def raw28005 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -3, 0]]
def raw28005Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28005step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![2, -1, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw28005step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28005step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw28005step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28005step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw28005step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28005 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28005 raw28005Labels = mixedMoment B node4633 node4633Labels := by
  calc
    mixedMoment B raw28005 raw28005Labels = mixedMoment B raw28005step0 raw28005step0Labels := by
      have ha : raw28005step0 = (fun i j => raw28005 (permutation686 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28005step0 raw28005; decide +kernel
      have hl : raw28005step0Labels = raw28005Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28005 raw28005Labels permutation686 permutation3
    mixedMoment B raw28005step0 raw28005step0Labels = mixedMoment B raw28005step1 raw28005step1Labels := by
      have ha : raw28005step1 = -raw28005step0 := by apply Matrix.ext; change ∀ i j, raw28005step1 i j = -(raw28005step0 i j); unfold raw28005step1 raw28005step0; decide +kernel
      have hl : raw28005step1Labels = raw28005step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28005step1 raw28005step1Labels = mixedMoment B raw28005step2 raw28005step2Labels := by
      have ha : raw28005step2 = raw28005step1 := by apply Matrix.ext; unfold raw28005step2 raw28005step1; decide +kernel
      have hl : raw28005step1Labels = labelEmbedding6 ∘ raw28005step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28005step1 raw28005step1Labels raw28005step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4633 node4633Labels := by rfl

def raw28006 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 2, -1], ![2, -1, -1], ![3, -3, 0]]
def raw28006Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28006step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 2, -1], ![2, -1, -1], ![3, -3, 0]]
def raw28006step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28006step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw28006step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28006step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw28006step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28006step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw28006step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28006 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28006 raw28006Labels = mixedMoment B node4650 node4650Labels := by
  calc
    mixedMoment B raw28006 raw28006Labels = mixedMoment B raw28006step0 raw28006step0Labels := by
      have hz : ∀ j, raw28006 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28006step0 = (fun i j => raw28006 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28006step0 raw28006; decide +kernel
      have hl : raw28006step0Labels = raw28006Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28006 raw28006Labels permutation346 hz
    mixedMoment B raw28006step0 raw28006step0Labels = mixedMoment B raw28006step1 raw28006step1Labels := by
      have ha : raw28006step1 = (fun i j => raw28006step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28006step1 raw28006step0; decide +kernel
      have hl : raw28006step1Labels = raw28006step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28006step0 raw28006step0Labels permutation149 permutation3
    mixedMoment B raw28006step1 raw28006step1Labels = mixedMoment B raw28006step2 raw28006step2Labels := by
      have ha : raw28006step2 = -raw28006step1 := by apply Matrix.ext; change ∀ i j, raw28006step2 i j = -(raw28006step1 i j); unfold raw28006step2 raw28006step1; decide +kernel
      have hl : raw28006step2Labels = raw28006step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28006step2 raw28006step2Labels = mixedMoment B raw28006step3 raw28006step3Labels := by
      have ha : raw28006step3 = raw28006step2 := by apply Matrix.ext; unfold raw28006step3 raw28006step2; decide +kernel
      have hl : raw28006step2Labels = labelEmbedding6 ∘ raw28006step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28006step2 raw28006step2Labels raw28006step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4650 node4650Labels := by rfl

def raw28007 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![4, -4, 0]]
def raw28007Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28007step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![4, -4, 0]]
def raw28007step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28007step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2], ![-3, 2, 1]]
def raw28007step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28007step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def raw28007step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28007step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def raw28007step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28007 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28007 raw28007Labels = mixedMoment B node4205 node4205Labels := by
  calc
    mixedMoment B raw28007 raw28007Labels = mixedMoment B raw28007step0 raw28007step0Labels := by
      have hz : ∀ j, raw28007 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28007step0 = (fun i j => raw28007 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28007step0 raw28007; decide +kernel
      have hl : raw28007step0Labels = raw28007Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28007 raw28007Labels permutation346 hz
    mixedMoment B raw28007step0 raw28007step0Labels = mixedMoment B raw28007step1 raw28007step1Labels := by
      have ha : raw28007step1 = (fun i j => raw28007step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28007step1 raw28007step0; decide +kernel
      have hl : raw28007step1Labels = raw28007step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28007step0 raw28007step0Labels permutation151 permutation3
    mixedMoment B raw28007step1 raw28007step1Labels = mixedMoment B raw28007step2 raw28007step2Labels := by
      have ha : raw28007step2 = -raw28007step1 := by apply Matrix.ext; change ∀ i j, raw28007step2 i j = -(raw28007step1 i j); unfold raw28007step2 raw28007step1; decide +kernel
      have hl : raw28007step2Labels = raw28007step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28007step2 raw28007step2Labels = mixedMoment B raw28007step3 raw28007step3Labels := by
      have ha : raw28007step3 = raw28007step2 := by apply Matrix.ext; unfold raw28007step3 raw28007step2; decide +kernel
      have hl : raw28007step2Labels = labelEmbedding6 ∘ raw28007step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28007step2 raw28007step2Labels raw28007step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4205 node4205Labels := by rfl

def raw28008 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![4, -4, 0]]
def raw28008Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28008step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw28008step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28008step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw28008step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28008step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw28008step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28008 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28008 raw28008Labels = mixedMoment B node4199 node4199Labels := by
  calc
    mixedMoment B raw28008 raw28008Labels = mixedMoment B raw28008step0 raw28008step0Labels := by
      have ha : raw28008step0 = (fun i j => raw28008 (permutation686 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28008step0 raw28008; decide +kernel
      have hl : raw28008step0Labels = raw28008Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28008 raw28008Labels permutation686 permutation3
    mixedMoment B raw28008step0 raw28008step0Labels = mixedMoment B raw28008step1 raw28008step1Labels := by
      have ha : raw28008step1 = -raw28008step0 := by apply Matrix.ext; change ∀ i j, raw28008step1 i j = -(raw28008step0 i j); unfold raw28008step1 raw28008step0; decide +kernel
      have hl : raw28008step1Labels = raw28008step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28008step1 raw28008step1Labels = mixedMoment B raw28008step2 raw28008step2Labels := by
      have ha : raw28008step2 = raw28008step1 := by apply Matrix.ext; unfold raw28008step2 raw28008step1; decide +kernel
      have hl : raw28008step1Labels = labelEmbedding6 ∘ raw28008step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28008step1 raw28008step1Labels raw28008step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4199 node4199Labels := by rfl

def raw28009 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 2, -1], ![1, 0, -1], ![4, -4, 0]]
def raw28009Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28009step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, 0, -1], ![4, -4, 0]]
def raw28009step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28009step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw28009step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28009step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw28009step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28009step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw28009step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28009 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28009 raw28009Labels = mixedMoment B node4219 node4219Labels := by
  calc
    mixedMoment B raw28009 raw28009Labels = mixedMoment B raw28009step0 raw28009step0Labels := by
      have hz : ∀ j, raw28009 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28009step0 = (fun i j => raw28009 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28009step0 raw28009; decide +kernel
      have hl : raw28009step0Labels = raw28009Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28009 raw28009Labels permutation346 hz
    mixedMoment B raw28009step0 raw28009step0Labels = mixedMoment B raw28009step1 raw28009step1Labels := by
      have ha : raw28009step1 = (fun i j => raw28009step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28009step1 raw28009step0; decide +kernel
      have hl : raw28009step1Labels = raw28009step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28009step0 raw28009step0Labels permutation149 permutation3
    mixedMoment B raw28009step1 raw28009step1Labels = mixedMoment B raw28009step2 raw28009step2Labels := by
      have ha : raw28009step2 = -raw28009step1 := by apply Matrix.ext; change ∀ i j, raw28009step2 i j = -(raw28009step1 i j); unfold raw28009step2 raw28009step1; decide +kernel
      have hl : raw28009step2Labels = raw28009step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28009step2 raw28009step2Labels = mixedMoment B raw28009step3 raw28009step3Labels := by
      have ha : raw28009step3 = raw28009step2 := by apply Matrix.ext; unfold raw28009step3 raw28009step2; decide +kernel
      have hl : raw28009step2Labels = labelEmbedding6 ∘ raw28009step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28009step2 raw28009step2Labels raw28009step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4219 node4219Labels := by rfl

def raw28010 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw28010Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28010step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2], ![-3, 2, 1]]
def raw28010step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28010step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def raw28010step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28010 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28010 raw28010Labels = mixedMoment B node1861 node1861Labels := by
  calc
    mixedMoment B raw28010 raw28010Labels = mixedMoment B raw28010step0 raw28010step0Labels := by
      have ha : raw28010step0 = (fun i j => raw28010 (permutation646 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28010step0 raw28010; decide +kernel
      have hl : raw28010step0Labels = raw28010Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28010 raw28010Labels permutation646 permutation3
    mixedMoment B raw28010step0 raw28010step0Labels = mixedMoment B raw28010step1 raw28010step1Labels := by
      have ha : raw28010step1 = -raw28010step0 := by apply Matrix.ext; change ∀ i j, raw28010step1 i j = -(raw28010step0 i j); unfold raw28010step1 raw28010step0; decide +kernel
      have hl : raw28010step1Labels = raw28010step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1861 node1861Labels := by rfl

def raw28011 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![-1, 2, -1], ![1, 0, -1], ![3, -3, 0]]
def raw28011Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28011step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw28011step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28011step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw28011step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28011 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28011 raw28011Labels = mixedMoment B node1867 node1867Labels := by
  calc
    mixedMoment B raw28011 raw28011Labels = mixedMoment B raw28011step0 raw28011step0Labels := by
      have ha : raw28011step0 = (fun i j => raw28011 (permutation644 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28011step0 raw28011; decide +kernel
      have hl : raw28011step0Labels = raw28011Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28011 raw28011Labels permutation644 permutation3
    mixedMoment B raw28011step0 raw28011step0Labels = mixedMoment B raw28011step1 raw28011step1Labels := by
      have ha : raw28011step1 = -raw28011step0 := by apply Matrix.ext; change ∀ i j, raw28011step1 i j = -(raw28011step0 i j); unfold raw28011step1 raw28011step0; decide +kernel
      have hl : raw28011step1Labels = raw28011step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1867 node1867Labels := by rfl

def raw28012 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw28012Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28012step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw28012step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28012step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2], ![-3, 2, 1]]
def raw28012step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28012step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw28012step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28012 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28012 raw28012Labels = mixedMoment B node1970 node1970Labels := by
  calc
    mixedMoment B raw28012 raw28012Labels = mixedMoment B raw28012step0 raw28012step0Labels := by
      have hz : ∀ j, raw28012 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28012step0 = (fun i j => raw28012 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28012step0 raw28012; decide +kernel
      have hl : raw28012step0Labels = raw28012Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28012 raw28012Labels permutation346 hz
    mixedMoment B raw28012step0 raw28012step0Labels = mixedMoment B raw28012step1 raw28012step1Labels := by
      have ha : raw28012step1 = (fun i j => raw28012step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28012step1 raw28012step0; decide +kernel
      have hl : raw28012step1Labels = raw28012step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28012step0 raw28012step0Labels permutation145 permutation3
    mixedMoment B raw28012step1 raw28012step1Labels = mixedMoment B raw28012step2 raw28012step2Labels := by
      have ha : raw28012step2 = -raw28012step1 := by apply Matrix.ext; change ∀ i j, raw28012step2 i j = -(raw28012step1 i j); unfold raw28012step2 raw28012step1; decide +kernel
      have hl : raw28012step2Labels = raw28012step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1970 node1970Labels := by rfl

def raw28013 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw28013Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28013step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw28013step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28013step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw28013step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28013 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28013 raw28013Labels = mixedMoment B node1964 node1964Labels := by
  calc
    mixedMoment B raw28013 raw28013Labels = mixedMoment B raw28013step0 raw28013step0Labels := by
      have ha : raw28013step0 = (fun i j => raw28013 (permutation662 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28013step0 raw28013; decide +kernel
      have hl : raw28013step0Labels = raw28013Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28013 raw28013Labels permutation662 permutation3
    mixedMoment B raw28013step0 raw28013step0Labels = mixedMoment B raw28013step1 raw28013step1Labels := by
      have ha : raw28013step1 = -raw28013step0 := by apply Matrix.ext; change ∀ i j, raw28013step1 i j = -(raw28013step0 i j); unfold raw28013step1 raw28013step0; decide +kernel
      have hl : raw28013step1Labels = raw28013step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1964 node1964Labels := by rfl

def raw28014 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![3, -3, 0]]
def raw28014Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28014step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 1, -1], ![2, -1, -1], ![3, -3, 0]]
def raw28014step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28014step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -1, -1], ![0, -1, 1], ![-2, 0, 2], ![-3, 2, 1]]
def raw28014step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28014step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def raw28014step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28014 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28014 raw28014Labels = mixedMoment B node1767 node1767Labels := by
  calc
    mixedMoment B raw28014 raw28014Labels = mixedMoment B raw28014step0 raw28014step0Labels := by
      have hz : ∀ j, raw28014 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28014step0 = (fun i j => raw28014 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28014step0 raw28014; decide +kernel
      have hl : raw28014step0Labels = raw28014Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28014 raw28014Labels permutation346 hz
    mixedMoment B raw28014step0 raw28014step0Labels = mixedMoment B raw28014step1 raw28014step1Labels := by
      have ha : raw28014step1 = (fun i j => raw28014step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28014step1 raw28014step0; decide +kernel
      have hl : raw28014step1Labels = raw28014step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28014step0 raw28014step0Labels permutation151 permutation3
    mixedMoment B raw28014step1 raw28014step1Labels = mixedMoment B raw28014step2 raw28014step2Labels := by
      have ha : raw28014step2 = -raw28014step1 := by apply Matrix.ext; change ∀ i j, raw28014step2 i j = -(raw28014step1 i j); unfold raw28014step2 raw28014step1; decide +kernel
      have hl : raw28014step2Labels = raw28014step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1767 node1767Labels := by rfl

def raw28015 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -3, 0]]
def raw28015Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28015step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![2, -1, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw28015step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28015step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw28015step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28015 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28015 raw28015Labels = mixedMoment B node1762 node1762Labels := by
  calc
    mixedMoment B raw28015 raw28015Labels = mixedMoment B raw28015step0 raw28015step0Labels := by
      have ha : raw28015step0 = (fun i j => raw28015 (permutation686 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28015step0 raw28015; decide +kernel
      have hl : raw28015step0Labels = raw28015Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28015 raw28015Labels permutation686 permutation3
    mixedMoment B raw28015step0 raw28015step0Labels = mixedMoment B raw28015step1 raw28015step1Labels := by
      have ha : raw28015step1 = -raw28015step0 := by apply Matrix.ext; change ∀ i j, raw28015step1 i j = -(raw28015step0 i j); unfold raw28015step1 raw28015step0; decide +kernel
      have hl : raw28015step1Labels = raw28015step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1762 node1762Labels := by rfl

def raw28016 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 2, -1], ![2, -1, -1], ![3, -3, 0]]
def raw28016Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28016step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 2, -1], ![2, -1, -1], ![3, -3, 0]]
def raw28016step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28016step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw28016step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28016step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw28016step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28016 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28016 raw28016Labels = mixedMoment B node1778 node1778Labels := by
  calc
    mixedMoment B raw28016 raw28016Labels = mixedMoment B raw28016step0 raw28016step0Labels := by
      have hz : ∀ j, raw28016 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28016step0 = (fun i j => raw28016 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28016step0 raw28016; decide +kernel
      have hl : raw28016step0Labels = raw28016Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28016 raw28016Labels permutation346 hz
    mixedMoment B raw28016step0 raw28016step0Labels = mixedMoment B raw28016step1 raw28016step1Labels := by
      have ha : raw28016step1 = (fun i j => raw28016step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28016step1 raw28016step0; decide +kernel
      have hl : raw28016step1Labels = raw28016step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28016step0 raw28016step0Labels permutation149 permutation3
    mixedMoment B raw28016step1 raw28016step1Labels = mixedMoment B raw28016step2 raw28016step2Labels := by
      have ha : raw28016step2 = -raw28016step1 := by apply Matrix.ext; change ∀ i j, raw28016step2 i j = -(raw28016step1 i j); unfold raw28016step2 raw28016step1; decide +kernel
      have hl : raw28016step2Labels = raw28016step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1778 node1778Labels := by rfl

def raw28017 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![4, -4, 0]]
def raw28017Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28017step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![4, -4, 0]]
def raw28017step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28017step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2], ![-3, 2, 1]]
def raw28017step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28017step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def raw28017step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28017 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28017 raw28017Labels = mixedMoment B node708 node708Labels := by
  calc
    mixedMoment B raw28017 raw28017Labels = mixedMoment B raw28017step0 raw28017step0Labels := by
      have hz : ∀ j, raw28017 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28017step0 = (fun i j => raw28017 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28017step0 raw28017; decide +kernel
      have hl : raw28017step0Labels = raw28017Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28017 raw28017Labels permutation346 hz
    mixedMoment B raw28017step0 raw28017step0Labels = mixedMoment B raw28017step1 raw28017step1Labels := by
      have ha : raw28017step1 = (fun i j => raw28017step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28017step1 raw28017step0; decide +kernel
      have hl : raw28017step1Labels = raw28017step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28017step0 raw28017step0Labels permutation151 permutation3
    mixedMoment B raw28017step1 raw28017step1Labels = mixedMoment B raw28017step2 raw28017step2Labels := by
      have ha : raw28017step2 = -raw28017step1 := by apply Matrix.ext; change ∀ i j, raw28017step2 i j = -(raw28017step1 i j); unfold raw28017step2 raw28017step1; decide +kernel
      have hl : raw28017step2Labels = raw28017step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node708 node708Labels := by rfl

def raw28018 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![4, -4, 0]]
def raw28018Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28018step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw28018step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28018step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw28018step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28018 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28018 raw28018Labels = mixedMoment B node702 node702Labels := by
  calc
    mixedMoment B raw28018 raw28018Labels = mixedMoment B raw28018step0 raw28018step0Labels := by
      have ha : raw28018step0 = (fun i j => raw28018 (permutation686 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28018step0 raw28018; decide +kernel
      have hl : raw28018step0Labels = raw28018Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28018 raw28018Labels permutation686 permutation3
    mixedMoment B raw28018step0 raw28018step0Labels = mixedMoment B raw28018step1 raw28018step1Labels := by
      have ha : raw28018step1 = -raw28018step0 := by apply Matrix.ext; change ∀ i j, raw28018step1 i j = -(raw28018step0 i j); unfold raw28018step1 raw28018step0; decide +kernel
      have hl : raw28018step1Labels = raw28018step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node702 node702Labels := by rfl

def raw28019 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 2, -1], ![1, 0, -1], ![4, -4, 0]]
def raw28019Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28019step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, 0, -1], ![4, -4, 0]]
def raw28019step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28019step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw28019step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28019step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw28019step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28019 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28019 raw28019Labels = mixedMoment B node720 node720Labels := by
  calc
    mixedMoment B raw28019 raw28019Labels = mixedMoment B raw28019step0 raw28019step0Labels := by
      have hz : ∀ j, raw28019 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28019step0 = (fun i j => raw28019 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28019step0 raw28019; decide +kernel
      have hl : raw28019step0Labels = raw28019Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28019 raw28019Labels permutation346 hz
    mixedMoment B raw28019step0 raw28019step0Labels = mixedMoment B raw28019step1 raw28019step1Labels := by
      have ha : raw28019step1 = (fun i j => raw28019step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28019step1 raw28019step0; decide +kernel
      have hl : raw28019step1Labels = raw28019step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28019step0 raw28019step0Labels permutation149 permutation3
    mixedMoment B raw28019step1 raw28019step1Labels = mixedMoment B raw28019step2 raw28019step2Labels := by
      have ha : raw28019step2 = -raw28019step1 := by apply Matrix.ext; change ∀ i j, raw28019step2 i j = -(raw28019step1 i j); unfold raw28019step2 raw28019step1; decide +kernel
      have hl : raw28019step2Labels = raw28019step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node720 node720Labels := by rfl

def raw28020 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28020Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28020step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28020step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28020step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw28020step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28020step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw28020step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28020 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28020 raw28020Labels = mixedMoment B node4811 node4811Labels := by
  calc
    mixedMoment B raw28020 raw28020Labels = mixedMoment B raw28020step0 raw28020step0Labels := by
      have hz : ∀ j, raw28020 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28020step0 = (fun i j => raw28020 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28020step0 raw28020; decide +kernel
      have hl : raw28020step0Labels = raw28020Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28020 raw28020Labels permutation346 hz
    mixedMoment B raw28020step0 raw28020step0Labels = mixedMoment B raw28020step1 raw28020step1Labels := by
      have ha : raw28020step1 = (fun i j => raw28020step0 (permutation150 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28020step1 raw28020step0; decide +kernel
      have hl : raw28020step1Labels = raw28020step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28020step0 raw28020step0Labels permutation150 permutation2
    mixedMoment B raw28020step1 raw28020step1Labels = mixedMoment B raw28020step2 raw28020step2Labels := by
      have ha : raw28020step2 = -raw28020step1 := by apply Matrix.ext; change ∀ i j, raw28020step2 i j = -(raw28020step1 i j); unfold raw28020step2 raw28020step1; decide +kernel
      have hl : raw28020step2Labels = raw28020step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4811 node4811Labels := by rfl

def raw28021 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28021Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28021step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw28021step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28021step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw28021step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28021 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28021 raw28021Labels = mixedMoment B node4802 node4802Labels := by
  calc
    mixedMoment B raw28021 raw28021Labels = mixedMoment B raw28021step0 raw28021step0Labels := by
      have ha : raw28021step0 = (fun i j => raw28021 (permutation688 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28021step0 raw28021; decide +kernel
      have hl : raw28021step0Labels = raw28021Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28021 raw28021Labels permutation688 permutation2
    mixedMoment B raw28021step0 raw28021step0Labels = mixedMoment B raw28021step1 raw28021step1Labels := by
      have ha : raw28021step1 = -raw28021step0 := by apply Matrix.ext; change ∀ i j, raw28021step1 i j = -(raw28021step0 i j); unfold raw28021step1 raw28021step0; decide +kernel
      have hl : raw28021step1Labels = raw28021step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4802 node4802Labels := by rfl

def raw28022 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28022Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28022step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28022step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28022step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw28022step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28022step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw28022step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28022 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28022 raw28022Labels = mixedMoment B node4838 node4838Labels := by
  calc
    mixedMoment B raw28022 raw28022Labels = mixedMoment B raw28022step0 raw28022step0Labels := by
      have hz : ∀ j, raw28022 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28022step0 = (fun i j => raw28022 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28022step0 raw28022; decide +kernel
      have hl : raw28022step0Labels = raw28022Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28022 raw28022Labels permutation346 hz
    mixedMoment B raw28022step0 raw28022step0Labels = mixedMoment B raw28022step1 raw28022step1Labels := by
      have ha : raw28022step1 = (fun i j => raw28022step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28022step1 raw28022step0; decide +kernel
      have hl : raw28022step1Labels = raw28022step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28022step0 raw28022step0Labels permutation149 permutation2
    mixedMoment B raw28022step1 raw28022step1Labels = mixedMoment B raw28022step2 raw28022step2Labels := by
      have ha : raw28022step2 = -raw28022step1 := by apply Matrix.ext; change ∀ i j, raw28022step2 i j = -(raw28022step1 i j); unfold raw28022step2 raw28022step1; decide +kernel
      have hl : raw28022step2Labels = raw28022step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4838 node4838Labels := by rfl

def raw28023 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![3, 0, -3]]
def raw28023Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28023step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw28023step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28023step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![3, 0, -3]]
def raw28023step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28023step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw28023step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28023step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw28023step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28023 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28023 raw28023Labels = mixedMoment B node4895 node4895Labels := by
  calc
    mixedMoment B raw28023 raw28023Labels = mixedMoment B raw28023step0 raw28023step0Labels := by
      have hz : ∀ j, raw28023 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw28023step0 = (fun i j => raw28023 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw28023step0 raw28023; decide +kernel
      have hl : raw28023step0Labels = raw28023Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28023 raw28023Labels permutation520 hz
    mixedMoment B raw28023step0 raw28023step0Labels = mixedMoment B raw28023step1 raw28023step1Labels := by
      have hz : ∀ j, raw28023step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28023step1 = (fun i j => raw28023step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28023step1 raw28023step0; decide +kernel
      have hl : raw28023step1Labels = raw28023step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28023step0 raw28023step0Labels permutation80 hz
    mixedMoment B raw28023step1 raw28023step1Labels = mixedMoment B raw28023step2 raw28023step2Labels := by
      have ha : raw28023step2 = (fun i j => raw28023step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28023step2 raw28023step1; decide +kernel
      have hl : raw28023step2Labels = raw28023step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28023step1 raw28023step1Labels permutation31 permutation2
    mixedMoment B raw28023step2 raw28023step2Labels = mixedMoment B raw28023step3 raw28023step3Labels := by
      have ha : raw28023step3 = -raw28023step2 := by apply Matrix.ext; change ∀ i j, raw28023step3 i j = -(raw28023step2 i j); unfold raw28023step3 raw28023step2; decide +kernel
      have hl : raw28023step3Labels = raw28023step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4895 node4895Labels := by rfl

def raw28024 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw28024Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28024step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw28024step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28024step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw28024step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw28024step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw28024step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28024 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28024 raw28024Labels = mixedMoment B node5271 node5271Labels := by
  calc
    mixedMoment B raw28024 raw28024Labels = mixedMoment B raw28024step0 raw28024step0Labels := by
      have hz : ∀ j, raw28024 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28024step0 = (fun i j => raw28024 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28024step0 raw28024; decide +kernel
      have hl : raw28024step0Labels = raw28024Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28024 raw28024Labels permutation346 hz
    mixedMoment B raw28024step0 raw28024step0Labels = mixedMoment B raw28024step1 raw28024step1Labels := by
      have ha : raw28024step1 = (fun i j => raw28024step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28024step1 raw28024step0; decide +kernel
      have hl : raw28024step1Labels = raw28024step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28024step0 raw28024step0Labels permutation151 permutation7
    mixedMoment B raw28024step1 raw28024step1Labels = mixedMoment B raw28024step2 raw28024step2Labels := by
      have ha : raw28024step2 = raw28024step1 := by apply Matrix.ext; unfold raw28024step2 raw28024step1; decide +kernel
      have hl : raw28024step1Labels = labelEmbedding10 ∘ raw28024step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28024step1 raw28024step1Labels raw28024step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5271 node5271Labels := by rfl

def raw28025 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28025Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28025step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28025step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28025step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw28025step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28025step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw28025step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28025 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28025 raw28025Labels = mixedMoment B node4442 node4442Labels := by
  calc
    mixedMoment B raw28025 raw28025Labels = mixedMoment B raw28025step0 raw28025step0Labels := by
      have hz : ∀ j, raw28025 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28025step0 = (fun i j => raw28025 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28025step0 raw28025; decide +kernel
      have hl : raw28025step0Labels = raw28025Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28025 raw28025Labels permutation346 hz
    mixedMoment B raw28025step0 raw28025step0Labels = mixedMoment B raw28025step1 raw28025step1Labels := by
      have ha : raw28025step1 = (fun i j => raw28025step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28025step1 raw28025step0; decide +kernel
      have hl : raw28025step1Labels = raw28025step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28025step0 raw28025step0Labels permutation32 permutation3
    mixedMoment B raw28025step1 raw28025step1Labels = mixedMoment B raw28025step2 raw28025step2Labels := by
      have ha : raw28025step2 = raw28025step1 := by apply Matrix.ext; unfold raw28025step2 raw28025step1; decide +kernel
      have hl : raw28025step1Labels = labelEmbedding6 ∘ raw28025step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28025step1 raw28025step1Labels raw28025step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4442 node4442Labels := by rfl

def raw28026 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28026Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28026step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 2, 1]]
def raw28026step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28026step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw28026step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28026 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28026 raw28026Labels = mixedMoment B node4792 node4792Labels := by
  calc
    mixedMoment B raw28026 raw28026Labels = mixedMoment B raw28026step0 raw28026step0Labels := by
      have ha : raw28026step0 = (fun i j => raw28026 (permutation676 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28026step0 raw28026; decide +kernel
      have hl : raw28026step0Labels = raw28026Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28026 raw28026Labels permutation676 permutation2
    mixedMoment B raw28026step0 raw28026step0Labels = mixedMoment B raw28026step1 raw28026step1Labels := by
      have ha : raw28026step1 = -raw28026step0 := by apply Matrix.ext; change ∀ i j, raw28026step1 i j = -(raw28026step0 i j); unfold raw28026step1 raw28026step0; decide +kernel
      have hl : raw28026step1Labels = raw28026step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4792 node4792Labels := by rfl

def raw28027 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28027Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28027step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28027step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28027step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw28027step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28027step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw28027step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28027 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28027 raw28027Labels = mixedMoment B node4807 node4807Labels := by
  calc
    mixedMoment B raw28027 raw28027Labels = mixedMoment B raw28027step0 raw28027step0Labels := by
      have hz : ∀ j, raw28027 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28027step0 = (fun i j => raw28027 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28027step0 raw28027; decide +kernel
      have hl : raw28027step0Labels = raw28027Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28027 raw28027Labels permutation346 hz
    mixedMoment B raw28027step0 raw28027step0Labels = mixedMoment B raw28027step1 raw28027step1Labels := by
      have ha : raw28027step1 = (fun i j => raw28027step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28027step1 raw28027step0; decide +kernel
      have hl : raw28027step1Labels = raw28027step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28027step0 raw28027step0Labels permutation149 permutation2
    mixedMoment B raw28027step1 raw28027step1Labels = mixedMoment B raw28027step2 raw28027step2Labels := by
      have ha : raw28027step2 = -raw28027step1 := by apply Matrix.ext; change ∀ i j, raw28027step2 i j = -(raw28027step1 i j); unfold raw28027step2 raw28027step1; decide +kernel
      have hl : raw28027step2Labels = raw28027step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4807 node4807Labels := by rfl

def raw28028 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![3, 0, -3]]
def raw28028Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28028step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw28028step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28028step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![3, 0, -3]]
def raw28028step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28028step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw28028step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28028step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw28028step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28028 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28028 raw28028Labels = mixedMoment B node4890 node4890Labels := by
  calc
    mixedMoment B raw28028 raw28028Labels = mixedMoment B raw28028step0 raw28028step0Labels := by
      have hz : ∀ j, raw28028 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw28028step0 = (fun i j => raw28028 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw28028step0 raw28028; decide +kernel
      have hl : raw28028step0Labels = raw28028Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28028 raw28028Labels permutation520 hz
    mixedMoment B raw28028step0 raw28028step0Labels = mixedMoment B raw28028step1 raw28028step1Labels := by
      have hz : ∀ j, raw28028step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28028step1 = (fun i j => raw28028step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28028step1 raw28028step0; decide +kernel
      have hl : raw28028step1Labels = raw28028step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28028step0 raw28028step0Labels permutation80 hz
    mixedMoment B raw28028step1 raw28028step1Labels = mixedMoment B raw28028step2 raw28028step2Labels := by
      have ha : raw28028step2 = (fun i j => raw28028step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28028step2 raw28028step1; decide +kernel
      have hl : raw28028step2Labels = raw28028step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28028step1 raw28028step1Labels permutation29 permutation2
    mixedMoment B raw28028step2 raw28028step2Labels = mixedMoment B raw28028step3 raw28028step3Labels := by
      have ha : raw28028step3 = -raw28028step2 := by apply Matrix.ext; change ∀ i j, raw28028step3 i j = -(raw28028step2 i j); unfold raw28028step3 raw28028step2; decide +kernel
      have hl : raw28028step3Labels = raw28028step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4890 node4890Labels := by rfl

def raw28029 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw28029Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28029step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw28029step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28029step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw28029step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw28029step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw28029step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28029 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28029 raw28029Labels = mixedMoment B node5270 node5270Labels := by
  calc
    mixedMoment B raw28029 raw28029Labels = mixedMoment B raw28029step0 raw28029step0Labels := by
      have hz : ∀ j, raw28029 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28029step0 = (fun i j => raw28029 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28029step0 raw28029; decide +kernel
      have hl : raw28029step0Labels = raw28029Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28029 raw28029Labels permutation346 hz
    mixedMoment B raw28029step0 raw28029step0Labels = mixedMoment B raw28029step1 raw28029step1Labels := by
      have ha : raw28029step1 = (fun i j => raw28029step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28029step1 raw28029step0; decide +kernel
      have hl : raw28029step1Labels = raw28029step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28029step0 raw28029step0Labels permutation149 permutation7
    mixedMoment B raw28029step1 raw28029step1Labels = mixedMoment B raw28029step2 raw28029step2Labels := by
      have ha : raw28029step2 = raw28029step1 := by apply Matrix.ext; unfold raw28029step2 raw28029step1; decide +kernel
      have hl : raw28029step1Labels = labelEmbedding10 ∘ raw28029step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28029step1 raw28029step1Labels raw28029step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5270 node5270Labels := by rfl

def raw28030 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28030Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28030step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw28030step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28030step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw28030step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28030 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28030 raw28030Labels = mixedMoment B node4331 node4331Labels := by
  calc
    mixedMoment B raw28030 raw28030Labels = mixedMoment B raw28030step0 raw28030step0Labels := by
      have ha : raw28030step0 = (fun i j => raw28030 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28030step0 raw28030; decide +kernel
      have hl : raw28030step0Labels = raw28030Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28030 raw28030Labels permutation158 permutation3
    mixedMoment B raw28030step0 raw28030step0Labels = mixedMoment B raw28030step1 raw28030step1Labels := by
      have ha : raw28030step1 = raw28030step0 := by apply Matrix.ext; unfold raw28030step1 raw28030step0; decide +kernel
      have hl : raw28030step0Labels = labelEmbedding6 ∘ raw28030step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28030step0 raw28030step0Labels raw28030step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4331 node4331Labels := by rfl

def raw28031 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28031Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28031step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-3, 2, 1]]
def raw28031step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28031step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw28031step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28031 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28031 raw28031Labels = mixedMoment B node4757 node4757Labels := by
  calc
    mixedMoment B raw28031 raw28031Labels = mixedMoment B raw28031step0 raw28031step0Labels := by
      have ha : raw28031step0 = (fun i j => raw28031 (permutation646 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28031step0 raw28031; decide +kernel
      have hl : raw28031step0Labels = raw28031Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28031 raw28031Labels permutation646 permutation2
    mixedMoment B raw28031step0 raw28031step0Labels = mixedMoment B raw28031step1 raw28031step1Labels := by
      have ha : raw28031step1 = -raw28031step0 := by apply Matrix.ext; change ∀ i j, raw28031step1 i j = -(raw28031step0 i j); unfold raw28031step1 raw28031step0; decide +kernel
      have hl : raw28031step1Labels = raw28031step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4757 node4757Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
