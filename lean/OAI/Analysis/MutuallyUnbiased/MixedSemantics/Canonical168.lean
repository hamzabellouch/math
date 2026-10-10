import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes8
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes9
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes11
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes12
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes13
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes14
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes23
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes29
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes66
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes69

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw21504 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21504Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21504step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21504step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21504step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21504step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21504 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21504 raw21504Labels = mixedMoment B node924 node924Labels := by
  calc
    mixedMoment B raw21504 raw21504Labels = mixedMoment B raw21504step0 raw21504step0Labels := by
      have hz : ∀ j, raw21504 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21504step0 = (fun i j => raw21504 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21504step0 raw21504; decide +kernel
      have hl : raw21504step0Labels = raw21504Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21504 raw21504Labels permutation434 hz
    mixedMoment B raw21504step0 raw21504step0Labels = mixedMoment B raw21504step1 raw21504step1Labels := by
      have ha : raw21504step1 = (fun i j => raw21504step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21504step1 raw21504step0; decide +kernel
      have hl : raw21504step1Labels = raw21504step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21504step0 raw21504step0Labels permutation34 permutation3
    _ = mixedMoment B node924 node924Labels := by rfl

def raw21505 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21505Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21505step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21505step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21505 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21505 raw21505Labels = mixedMoment B node865 node865Labels := by
  calc
    mixedMoment B raw21505 raw21505Labels = mixedMoment B raw21505step0 raw21505step0Labels := by
      have ha : raw21505step0 = (fun i j => raw21505 (permutation202 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21505step0 raw21505; decide +kernel
      have hl : raw21505step0Labels = raw21505Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21505 raw21505Labels permutation202 permutation3
    _ = mixedMoment B node865 node865Labels := by rfl

def raw21506 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw21506Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21506step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw21506step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21506step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw21506step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21506 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21506 raw21506Labels = mixedMoment B node1041 node1041Labels := by
  calc
    mixedMoment B raw21506 raw21506Labels = mixedMoment B raw21506step0 raw21506step0Labels := by
      have hz : ∀ j, raw21506 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21506step0 = (fun i j => raw21506 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21506step0 raw21506; decide +kernel
      have hl : raw21506step0Labels = raw21506Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21506 raw21506Labels permutation434 hz
    mixedMoment B raw21506step0 raw21506step0Labels = mixedMoment B raw21506step1 raw21506step1Labels := by
      have ha : raw21506step1 = (fun i j => raw21506step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21506step1 raw21506step0; decide +kernel
      have hl : raw21506step1Labels = raw21506step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21506step0 raw21506step0Labels permutation34 permutation3
    _ = mixedMoment B node1041 node1041Labels := by rfl

def raw21507 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21507Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21507step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21507step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21507step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21507step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21507 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21507 raw21507Labels = mixedMoment B node538 node538Labels := by
  calc
    mixedMoment B raw21507 raw21507Labels = mixedMoment B raw21507step0 raw21507step0Labels := by
      have hz : ∀ j, raw21507 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21507step0 = (fun i j => raw21507 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21507step0 raw21507; decide +kernel
      have hl : raw21507step0Labels = raw21507Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21507 raw21507Labels permutation346 hz
    mixedMoment B raw21507step0 raw21507step0Labels = mixedMoment B raw21507step1 raw21507step1Labels := by
      have ha : raw21507step1 = (fun i j => raw21507step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21507step1 raw21507step0; decide +kernel
      have hl : raw21507step1Labels = raw21507step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21507step0 raw21507step0Labels permutation34 permutation3
    _ = mixedMoment B node538 node538Labels := by rfl

def raw21508 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21508Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21508step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21508step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21508step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21508step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21508 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21508 raw21508Labels = mixedMoment B node924 node924Labels := by
  calc
    mixedMoment B raw21508 raw21508Labels = mixedMoment B raw21508step0 raw21508step0Labels := by
      have hz : ∀ j, raw21508 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21508step0 = (fun i j => raw21508 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21508step0 raw21508; decide +kernel
      have hl : raw21508step0Labels = raw21508Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21508 raw21508Labels permutation346 hz
    mixedMoment B raw21508step0 raw21508step0Labels = mixedMoment B raw21508step1 raw21508step1Labels := by
      have ha : raw21508step1 = (fun i j => raw21508step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21508step1 raw21508step0; decide +kernel
      have hl : raw21508step1Labels = raw21508step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21508step0 raw21508step0Labels permutation34 permutation3
    _ = mixedMoment B node924 node924Labels := by rfl

def raw21509 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21509Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21509step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21509step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21509 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21509 raw21509Labels = mixedMoment B node865 node865Labels := by
  calc
    mixedMoment B raw21509 raw21509Labels = mixedMoment B raw21509step0 raw21509step0Labels := by
      have ha : raw21509step0 = (fun i j => raw21509 (permutation178 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21509step0 raw21509; decide +kernel
      have hl : raw21509step0Labels = raw21509Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21509 raw21509Labels permutation178 permutation3
    _ = mixedMoment B node865 node865Labels := by rfl

def raw21510 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw21510Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21510step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw21510step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21510step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw21510step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21510 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21510 raw21510Labels = mixedMoment B node1041 node1041Labels := by
  calc
    mixedMoment B raw21510 raw21510Labels = mixedMoment B raw21510step0 raw21510step0Labels := by
      have hz : ∀ j, raw21510 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21510step0 = (fun i j => raw21510 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21510step0 raw21510; decide +kernel
      have hl : raw21510step0Labels = raw21510Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21510 raw21510Labels permutation346 hz
    mixedMoment B raw21510step0 raw21510step0Labels = mixedMoment B raw21510step1 raw21510step1Labels := by
      have ha : raw21510step1 = (fun i j => raw21510step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21510step1 raw21510step0; decide +kernel
      have hl : raw21510step1Labels = raw21510step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21510step0 raw21510step0Labels permutation34 permutation3
    _ = mixedMoment B node1041 node1041Labels := by rfl

def raw21511 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw21511Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21511step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw21511step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21511step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![2, -1, -1], ![3, -2, -1]]
def raw21511step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21511step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw21511step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21511 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21511 raw21511Labels = mixedMoment B node547 node547Labels := by
  calc
    mixedMoment B raw21511 raw21511Labels = mixedMoment B raw21511step0 raw21511step0Labels := by
      have hz : ∀ j, raw21511 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21511step0 = (fun i j => raw21511 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21511step0 raw21511; decide +kernel
      have hl : raw21511step0Labels = raw21511Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21511 raw21511Labels permutation434 hz
    mixedMoment B raw21511step0 raw21511step0Labels = mixedMoment B raw21511step1 raw21511step1Labels := by
      have hz : ∀ j, raw21511step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21511step1 = (fun i j => raw21511step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21511step1 raw21511step0; decide +kernel
      have hl : raw21511step1Labels = raw21511step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21511step0 raw21511step0Labels permutation80 hz
    mixedMoment B raw21511step1 raw21511step1Labels = mixedMoment B raw21511step2 raw21511step2Labels := by
      have ha : raw21511step2 = (fun i j => raw21511step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21511step2 raw21511step1; decide +kernel
      have hl : raw21511step2Labels = raw21511step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21511step1 raw21511step1Labels permutation8 permutation3
    _ = mixedMoment B node547 node547Labels := by rfl

def raw21512 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw21512Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21512step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw21512step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21512step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![2, -1, -1], ![3, -2, -1]]
def raw21512step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21512step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -1, -1], ![3, -1, -2]]
def raw21512step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21512 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21512 raw21512Labels = mixedMoment B node938 node938Labels := by
  calc
    mixedMoment B raw21512 raw21512Labels = mixedMoment B raw21512step0 raw21512step0Labels := by
      have hz : ∀ j, raw21512 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21512step0 = (fun i j => raw21512 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21512step0 raw21512; decide +kernel
      have hl : raw21512step0Labels = raw21512Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21512 raw21512Labels permutation434 hz
    mixedMoment B raw21512step0 raw21512step0Labels = mixedMoment B raw21512step1 raw21512step1Labels := by
      have hz : ∀ j, raw21512step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21512step1 = (fun i j => raw21512step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21512step1 raw21512step0; decide +kernel
      have hl : raw21512step1Labels = raw21512step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21512step0 raw21512step0Labels permutation80 hz
    mixedMoment B raw21512step1 raw21512step1Labels = mixedMoment B raw21512step2 raw21512step2Labels := by
      have ha : raw21512step2 = (fun i j => raw21512step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21512step2 raw21512step1; decide +kernel
      have hl : raw21512step2Labels = raw21512step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21512step1 raw21512step1Labels permutation8 permutation3
    _ = mixedMoment B node938 node938Labels := by rfl

def raw21513 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw21513Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21513step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw21513step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21513step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw21513step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21513 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21513 raw21513Labels = mixedMoment B node873 node873Labels := by
  calc
    mixedMoment B raw21513 raw21513Labels = mixedMoment B raw21513step0 raw21513step0Labels := by
      have hz : ∀ j, raw21513 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21513step0 = (fun i j => raw21513 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21513step0 raw21513; decide +kernel
      have hl : raw21513step0Labels = raw21513Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21513 raw21513Labels permutation434 hz
    mixedMoment B raw21513step0 raw21513step0Labels = mixedMoment B raw21513step1 raw21513step1Labels := by
      have ha : raw21513step1 = (fun i j => raw21513step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21513step1 raw21513step0; decide +kernel
      have hl : raw21513step1Labels = raw21513step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21513step0 raw21513step0Labels permutation38 permutation3
    _ = mixedMoment B node873 node873Labels := by rfl

def raw21514 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw21514Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21514step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw21514step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21514step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw21514step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21514 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21514 raw21514Labels = mixedMoment B node873 node873Labels := by
  calc
    mixedMoment B raw21514 raw21514Labels = mixedMoment B raw21514step0 raw21514step0Labels := by
      have hz : ∀ j, raw21514 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21514step0 = (fun i j => raw21514 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21514step0 raw21514; decide +kernel
      have hl : raw21514step0Labels = raw21514Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21514 raw21514Labels permutation346 hz
    mixedMoment B raw21514step0 raw21514step0Labels = mixedMoment B raw21514step1 raw21514step1Labels := by
      have ha : raw21514step1 = (fun i j => raw21514step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21514step1 raw21514step0; decide +kernel
      have hl : raw21514step1Labels = raw21514step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21514step0 raw21514step0Labels permutation38 permutation3
    _ = mixedMoment B node873 node873Labels := by rfl

def raw21515 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw21515Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21515step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw21515step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21515step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw21515step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21515step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw21515step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21515 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21515 raw21515Labels = mixedMoment B node1050 node1050Labels := by
  calc
    mixedMoment B raw21515 raw21515Labels = mixedMoment B raw21515step0 raw21515step0Labels := by
      have hz : ∀ j, raw21515 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21515step0 = (fun i j => raw21515 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21515step0 raw21515; decide +kernel
      have hl : raw21515step0Labels = raw21515Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21515 raw21515Labels permutation434 hz
    mixedMoment B raw21515step0 raw21515step0Labels = mixedMoment B raw21515step1 raw21515step1Labels := by
      have hz : ∀ j, raw21515step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21515step1 = (fun i j => raw21515step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21515step1 raw21515step0; decide +kernel
      have hl : raw21515step1Labels = raw21515step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21515step0 raw21515step0Labels permutation80 hz
    mixedMoment B raw21515step1 raw21515step1Labels = mixedMoment B raw21515step2 raw21515step2Labels := by
      have ha : raw21515step2 = (fun i j => raw21515step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21515step2 raw21515step1; decide +kernel
      have hl : raw21515step2Labels = raw21515step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21515step1 raw21515step1Labels permutation8 permutation3
    _ = mixedMoment B node1050 node1050Labels := by rfl

def raw21516 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![4, -3, -1]]
def raw21516Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21516step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![4, -3, -1]]
def raw21516step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21516step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![1, 0, -1], ![4, -3, -1]]
def raw21516step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21516step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![4, -1, -3]]
def raw21516step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21516 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21516 raw21516Labels = mixedMoment B node540 node540Labels := by
  calc
    mixedMoment B raw21516 raw21516Labels = mixedMoment B raw21516step0 raw21516step0Labels := by
      have hz : ∀ j, raw21516 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21516step0 = (fun i j => raw21516 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21516step0 raw21516; decide +kernel
      have hl : raw21516step0Labels = raw21516Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21516 raw21516Labels permutation434 hz
    mixedMoment B raw21516step0 raw21516step0Labels = mixedMoment B raw21516step1 raw21516step1Labels := by
      have hz : ∀ j, raw21516step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21516step1 = (fun i j => raw21516step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21516step1 raw21516step0; decide +kernel
      have hl : raw21516step1Labels = raw21516step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21516step0 raw21516step0Labels permutation80 hz
    mixedMoment B raw21516step1 raw21516step1Labels = mixedMoment B raw21516step2 raw21516step2Labels := by
      have ha : raw21516step2 = (fun i j => raw21516step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21516step2 raw21516step1; decide +kernel
      have hl : raw21516step2Labels = raw21516step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21516step1 raw21516step1Labels permutation8 permutation3
    _ = mixedMoment B node540 node540Labels := by rfl

def raw21517 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![4, -3, -1]]
def raw21517Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21517step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![4, -3, -1]]
def raw21517step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21517step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, 0, -1], ![4, -3, -1]]
def raw21517step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21517step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![4, -1, -3]]
def raw21517step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21517 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21517 raw21517Labels = mixedMoment B node928 node928Labels := by
  calc
    mixedMoment B raw21517 raw21517Labels = mixedMoment B raw21517step0 raw21517step0Labels := by
      have hz : ∀ j, raw21517 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21517step0 = (fun i j => raw21517 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21517step0 raw21517; decide +kernel
      have hl : raw21517step0Labels = raw21517Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21517 raw21517Labels permutation434 hz
    mixedMoment B raw21517step0 raw21517step0Labels = mixedMoment B raw21517step1 raw21517step1Labels := by
      have hz : ∀ j, raw21517step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21517step1 = (fun i j => raw21517step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21517step1 raw21517step0; decide +kernel
      have hl : raw21517step1Labels = raw21517step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21517step0 raw21517step0Labels permutation80 hz
    mixedMoment B raw21517step1 raw21517step1Labels = mixedMoment B raw21517step2 raw21517step2Labels := by
      have ha : raw21517step2 = (fun i j => raw21517step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21517step2 raw21517step1; decide +kernel
      have hl : raw21517step2Labels = raw21517step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21517step1 raw21517step1Labels permutation8 permutation3
    _ = mixedMoment B node928 node928Labels := by rfl

def raw21518 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![4, -3, -1]]
def raw21518Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21518step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![-1, 1, 0], ![1, 0, -1], ![4, -3, -1]]
def raw21518step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21518step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![4, -1, -3]]
def raw21518step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21518 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21518 raw21518Labels = mixedMoment B node867 node867Labels := by
  calc
    mixedMoment B raw21518 raw21518Labels = mixedMoment B raw21518step0 raw21518step0Labels := by
      have hz : ∀ j, raw21518 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21518step0 = (fun i j => raw21518 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21518step0 raw21518; decide +kernel
      have hl : raw21518step0Labels = raw21518Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21518 raw21518Labels permutation434 hz
    mixedMoment B raw21518step0 raw21518step0Labels = mixedMoment B raw21518step1 raw21518step1Labels := by
      have ha : raw21518step1 = (fun i j => raw21518step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21518step1 raw21518step0; decide +kernel
      have hl : raw21518step1Labels = raw21518step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21518step0 raw21518step0Labels permutation38 permutation3
    _ = mixedMoment B node867 node867Labels := by rfl

def raw21519 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![4, -3, -1]]
def raw21519Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21519step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![-1, 1, 0], ![1, 0, -1], ![4, -3, -1]]
def raw21519step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21519step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![4, -1, -3]]
def raw21519step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21519 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21519 raw21519Labels = mixedMoment B node867 node867Labels := by
  calc
    mixedMoment B raw21519 raw21519Labels = mixedMoment B raw21519step0 raw21519step0Labels := by
      have hz : ∀ j, raw21519 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21519step0 = (fun i j => raw21519 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21519step0 raw21519; decide +kernel
      have hl : raw21519step0Labels = raw21519Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21519 raw21519Labels permutation346 hz
    mixedMoment B raw21519step0 raw21519step0Labels = mixedMoment B raw21519step1 raw21519step1Labels := by
      have ha : raw21519step1 = (fun i j => raw21519step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21519step1 raw21519step0; decide +kernel
      have hl : raw21519step1Labels = raw21519step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21519step0 raw21519step0Labels permutation38 permutation3
    _ = mixedMoment B node867 node867Labels := by rfl

def raw21520 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw21520Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21520step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw21520step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21520step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw21520step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21520step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-2, 2, 0], ![-2, -1, 3]]
def raw21520step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw21520step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw21520step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw21520step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw21520step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21520 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21520 raw21520Labels = mixedMoment B node4272 node4272Labels := by
  calc
    mixedMoment B raw21520 raw21520Labels = mixedMoment B raw21520step0 raw21520step0Labels := by
      have hz : ∀ j, raw21520 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21520step0 = (fun i j => raw21520 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21520step0 raw21520; decide +kernel
      have hl : raw21520step0Labels = raw21520Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21520 raw21520Labels permutation434 hz
    mixedMoment B raw21520step0 raw21520step0Labels = mixedMoment B raw21520step1 raw21520step1Labels := by
      have hz : ∀ j, raw21520step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21520step1 = (fun i j => raw21520step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21520step1 raw21520step0; decide +kernel
      have hl : raw21520step1Labels = raw21520step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21520step0 raw21520step0Labels permutation80 hz
    mixedMoment B raw21520step1 raw21520step1Labels = mixedMoment B raw21520step2 raw21520step2Labels := by
      have ha : raw21520step2 = (fun i j => raw21520step1 (permutation10 i) (permutation4 j)) := by apply Matrix.ext; unfold raw21520step2 raw21520step1; decide +kernel
      have hl : raw21520step2Labels = raw21520step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21520step1 raw21520step1Labels permutation10 permutation4
    mixedMoment B raw21520step2 raw21520step2Labels = mixedMoment B raw21520step3 raw21520step3Labels := by
      have ha : raw21520step3 = -raw21520step2 := by apply Matrix.ext; change ∀ i j, raw21520step3 i j = -(raw21520step2 i j); unfold raw21520step3 raw21520step2; decide +kernel
      have hl : raw21520step3Labels = raw21520step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21520step3 raw21520step3Labels = mixedMoment B raw21520step4 raw21520step4Labels := by
      have ha : raw21520step4 = raw21520step3 := by apply Matrix.ext; unfold raw21520step4 raw21520step3; decide +kernel
      have hl : raw21520step3Labels = labelEmbedding7 ∘ raw21520step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21520step3 raw21520step3Labels raw21520step4Labels labelEmbedding7 hl
    _ = mixedMoment B node4272 node4272Labels := by rfl

def raw21521 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw21521Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21521step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw21521step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21521step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![3, -1, -2]]
def raw21521step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw21521step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![3, -1, -2]]
def raw21521step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21521 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21521 raw21521Labels = mixedMoment B node4408 node4408Labels := by
  calc
    mixedMoment B raw21521 raw21521Labels = mixedMoment B raw21521step0 raw21521step0Labels := by
      have hz : ∀ j, raw21521 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21521step0 = (fun i j => raw21521 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21521step0 raw21521; decide +kernel
      have hl : raw21521step0Labels = raw21521Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21521 raw21521Labels permutation434 hz
    mixedMoment B raw21521step0 raw21521step0Labels = mixedMoment B raw21521step1 raw21521step1Labels := by
      have ha : raw21521step1 = (fun i j => raw21521step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw21521step1 raw21521step0; decide +kernel
      have hl : raw21521step1Labels = raw21521step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21521step0 raw21521step0Labels permutation38 permutation6
    mixedMoment B raw21521step1 raw21521step1Labels = mixedMoment B raw21521step2 raw21521step2Labels := by
      have ha : raw21521step2 = raw21521step1 := by apply Matrix.ext; unfold raw21521step2 raw21521step1; decide +kernel
      have hl : raw21521step1Labels = labelEmbedding9 ∘ raw21521step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21521step1 raw21521step1Labels raw21521step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4408 node4408Labels := by rfl

def raw21522 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw21522Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21522step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw21522step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21522step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![3, -1, -2]]
def raw21522step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw21522step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![3, -1, -2]]
def raw21522step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21522 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21522 raw21522Labels = mixedMoment B node4408 node4408Labels := by
  calc
    mixedMoment B raw21522 raw21522Labels = mixedMoment B raw21522step0 raw21522step0Labels := by
      have hz : ∀ j, raw21522 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21522step0 = (fun i j => raw21522 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21522step0 raw21522; decide +kernel
      have hl : raw21522step0Labels = raw21522Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21522 raw21522Labels permutation346 hz
    mixedMoment B raw21522step0 raw21522step0Labels = mixedMoment B raw21522step1 raw21522step1Labels := by
      have ha : raw21522step1 = (fun i j => raw21522step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw21522step1 raw21522step0; decide +kernel
      have hl : raw21522step1Labels = raw21522step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21522step0 raw21522step0Labels permutation38 permutation6
    mixedMoment B raw21522step1 raw21522step1Labels = mixedMoment B raw21522step2 raw21522step2Labels := by
      have ha : raw21522step2 = raw21522step1 := by apply Matrix.ext; unfold raw21522step2 raw21522step1; decide +kernel
      have hl : raw21522step1Labels = labelEmbedding9 ∘ raw21522step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21522step1 raw21522step1Labels raw21522step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4408 node4408Labels := by rfl

def raw21523 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw21523Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21523step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw21523step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21523step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw21523step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21523step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -2, 1], ![3, -1, -2]]
def raw21523step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw21523step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -2, 1], ![3, -1, -2]]
def raw21523step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21523 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21523 raw21523Labels = mixedMoment B node4472 node4472Labels := by
  calc
    mixedMoment B raw21523 raw21523Labels = mixedMoment B raw21523step0 raw21523step0Labels := by
      have hz : ∀ j, raw21523 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21523step0 = (fun i j => raw21523 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21523step0 raw21523; decide +kernel
      have hl : raw21523step0Labels = raw21523Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21523 raw21523Labels permutation434 hz
    mixedMoment B raw21523step0 raw21523step0Labels = mixedMoment B raw21523step1 raw21523step1Labels := by
      have hz : ∀ j, raw21523step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21523step1 = (fun i j => raw21523step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21523step1 raw21523step0; decide +kernel
      have hl : raw21523step1Labels = raw21523step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21523step0 raw21523step0Labels permutation80 hz
    mixedMoment B raw21523step1 raw21523step1Labels = mixedMoment B raw21523step2 raw21523step2Labels := by
      have ha : raw21523step2 = (fun i j => raw21523step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw21523step2 raw21523step1; decide +kernel
      have hl : raw21523step2Labels = raw21523step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21523step1 raw21523step1Labels permutation8 permutation6
    mixedMoment B raw21523step2 raw21523step2Labels = mixedMoment B raw21523step3 raw21523step3Labels := by
      have ha : raw21523step3 = raw21523step2 := by apply Matrix.ext; unfold raw21523step3 raw21523step2; decide +kernel
      have hl : raw21523step2Labels = labelEmbedding9 ∘ raw21523step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21523step2 raw21523step2Labels raw21523step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4472 node4472Labels := by rfl

def raw21524 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw21524Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21524step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw21524step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21524step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw21524step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw21524step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw21524step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21524 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21524 raw21524Labels = mixedMoment B node4251 node4251Labels := by
  calc
    mixedMoment B raw21524 raw21524Labels = mixedMoment B raw21524step0 raw21524step0Labels := by
      have hz : ∀ j, raw21524 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21524step0 = (fun i j => raw21524 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21524step0 raw21524; decide +kernel
      have hl : raw21524step0Labels = raw21524Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21524 raw21524Labels permutation434 hz
    mixedMoment B raw21524step0 raw21524step0Labels = mixedMoment B raw21524step1 raw21524step1Labels := by
      have ha : raw21524step1 = (fun i j => raw21524step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw21524step1 raw21524step0; decide +kernel
      have hl : raw21524step1Labels = raw21524step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21524step0 raw21524step0Labels permutation32 permutation6
    mixedMoment B raw21524step1 raw21524step1Labels = mixedMoment B raw21524step2 raw21524step2Labels := by
      have ha : raw21524step2 = raw21524step1 := by apply Matrix.ext; unfold raw21524step2 raw21524step1; decide +kernel
      have hl : raw21524step1Labels = labelEmbedding9 ∘ raw21524step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21524step1 raw21524step1Labels raw21524step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4251 node4251Labels := by rfl

def raw21525 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw21525Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21525step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw21525step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw21525step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw21525step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21525 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21525 raw21525Labels = mixedMoment B node4390 node4390Labels := by
  calc
    mixedMoment B raw21525 raw21525Labels = mixedMoment B raw21525step0 raw21525step0Labels := by
      have ha : raw21525step0 = (fun i j => raw21525 (permutation200 i) (permutation6 j)) := by apply Matrix.ext; unfold raw21525step0 raw21525; decide +kernel
      have hl : raw21525step0Labels = raw21525Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21525 raw21525Labels permutation200 permutation6
    mixedMoment B raw21525step0 raw21525step0Labels = mixedMoment B raw21525step1 raw21525step1Labels := by
      have ha : raw21525step1 = raw21525step0 := by apply Matrix.ext; unfold raw21525step1 raw21525step0; decide +kernel
      have hl : raw21525step0Labels = labelEmbedding9 ∘ raw21525step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21525step0 raw21525step0Labels raw21525step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4390 node4390Labels := by rfl

def raw21526 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw21526Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21526step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw21526step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21526step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw21526step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw21526step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw21526step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21526 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21526 raw21526Labels = mixedMoment B node4437 node4437Labels := by
  calc
    mixedMoment B raw21526 raw21526Labels = mixedMoment B raw21526step0 raw21526step0Labels := by
      have hz : ∀ j, raw21526 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21526step0 = (fun i j => raw21526 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21526step0 raw21526; decide +kernel
      have hl : raw21526step0Labels = raw21526Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21526 raw21526Labels permutation434 hz
    mixedMoment B raw21526step0 raw21526step0Labels = mixedMoment B raw21526step1 raw21526step1Labels := by
      have ha : raw21526step1 = (fun i j => raw21526step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw21526step1 raw21526step0; decide +kernel
      have hl : raw21526step1Labels = raw21526step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21526step0 raw21526step0Labels permutation32 permutation6
    mixedMoment B raw21526step1 raw21526step1Labels = mixedMoment B raw21526step2 raw21526step2Labels := by
      have ha : raw21526step2 = raw21526step1 := by apply Matrix.ext; unfold raw21526step2 raw21526step1; decide +kernel
      have hl : raw21526step1Labels = labelEmbedding9 ∘ raw21526step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21526step1 raw21526step1Labels raw21526step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4437 node4437Labels := by rfl

def raw21527 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw21527Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21527step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw21527step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21527step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw21527step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw21527step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw21527step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21527 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21527 raw21527Labels = mixedMoment B node4251 node4251Labels := by
  calc
    mixedMoment B raw21527 raw21527Labels = mixedMoment B raw21527step0 raw21527step0Labels := by
      have hz : ∀ j, raw21527 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21527step0 = (fun i j => raw21527 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21527step0 raw21527; decide +kernel
      have hl : raw21527step0Labels = raw21527Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21527 raw21527Labels permutation346 hz
    mixedMoment B raw21527step0 raw21527step0Labels = mixedMoment B raw21527step1 raw21527step1Labels := by
      have ha : raw21527step1 = (fun i j => raw21527step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw21527step1 raw21527step0; decide +kernel
      have hl : raw21527step1Labels = raw21527step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21527step0 raw21527step0Labels permutation32 permutation6
    mixedMoment B raw21527step1 raw21527step1Labels = mixedMoment B raw21527step2 raw21527step2Labels := by
      have ha : raw21527step2 = raw21527step1 := by apply Matrix.ext; unfold raw21527step2 raw21527step1; decide +kernel
      have hl : raw21527step1Labels = labelEmbedding9 ∘ raw21527step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21527step1 raw21527step1Labels raw21527step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4251 node4251Labels := by rfl

def raw21528 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw21528Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21528step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw21528step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw21528step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw21528step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21528 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21528 raw21528Labels = mixedMoment B node4390 node4390Labels := by
  calc
    mixedMoment B raw21528 raw21528Labels = mixedMoment B raw21528step0 raw21528step0Labels := by
      have ha : raw21528step0 = (fun i j => raw21528 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw21528step0 raw21528; decide +kernel
      have hl : raw21528step0Labels = raw21528Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21528 raw21528Labels permutation176 permutation6
    mixedMoment B raw21528step0 raw21528step0Labels = mixedMoment B raw21528step1 raw21528step1Labels := by
      have ha : raw21528step1 = raw21528step0 := by apply Matrix.ext; unfold raw21528step1 raw21528step0; decide +kernel
      have hl : raw21528step0Labels = labelEmbedding9 ∘ raw21528step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21528step0 raw21528step0Labels raw21528step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4390 node4390Labels := by rfl

def raw21529 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw21529Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21529step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw21529step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21529step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw21529step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw21529step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw21529step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21529 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21529 raw21529Labels = mixedMoment B node4437 node4437Labels := by
  calc
    mixedMoment B raw21529 raw21529Labels = mixedMoment B raw21529step0 raw21529step0Labels := by
      have hz : ∀ j, raw21529 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21529step0 = (fun i j => raw21529 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21529step0 raw21529; decide +kernel
      have hl : raw21529step0Labels = raw21529Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21529 raw21529Labels permutation346 hz
    mixedMoment B raw21529step0 raw21529step0Labels = mixedMoment B raw21529step1 raw21529step1Labels := by
      have ha : raw21529step1 = (fun i j => raw21529step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw21529step1 raw21529step0; decide +kernel
      have hl : raw21529step1Labels = raw21529step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21529step0 raw21529step0Labels permutation32 permutation6
    mixedMoment B raw21529step1 raw21529step1Labels = mixedMoment B raw21529step2 raw21529step2Labels := by
      have ha : raw21529step2 = raw21529step1 := by apply Matrix.ext; unfold raw21529step2 raw21529step1; decide +kernel
      have hl : raw21529step1Labels = labelEmbedding9 ∘ raw21529step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21529step1 raw21529step1Labels raw21529step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4437 node4437Labels := by rfl

def raw21530 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw21530Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21530step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw21530step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21530step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw21530step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21530step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21530step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw21530step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21530step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21530 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21530 raw21530Labels = mixedMoment B node4463 node4463Labels := by
  calc
    mixedMoment B raw21530 raw21530Labels = mixedMoment B raw21530step0 raw21530step0Labels := by
      have hz : ∀ j, raw21530 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21530step0 = (fun i j => raw21530 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21530step0 raw21530; decide +kernel
      have hl : raw21530step0Labels = raw21530Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21530 raw21530Labels permutation434 hz
    mixedMoment B raw21530step0 raw21530step0Labels = mixedMoment B raw21530step1 raw21530step1Labels := by
      have hz : ∀ j, raw21530step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21530step1 = (fun i j => raw21530step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21530step1 raw21530step0; decide +kernel
      have hl : raw21530step1Labels = raw21530step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21530step0 raw21530step0Labels permutation80 hz
    mixedMoment B raw21530step1 raw21530step1Labels = mixedMoment B raw21530step2 raw21530step2Labels := by
      have ha : raw21530step2 = (fun i j => raw21530step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw21530step2 raw21530step1; decide +kernel
      have hl : raw21530step2Labels = raw21530step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21530step1 raw21530step1Labels permutation8 permutation6
    mixedMoment B raw21530step2 raw21530step2Labels = mixedMoment B raw21530step3 raw21530step3Labels := by
      have ha : raw21530step3 = raw21530step2 := by apply Matrix.ext; unfold raw21530step3 raw21530step2; decide +kernel
      have hl : raw21530step2Labels = labelEmbedding9 ∘ raw21530step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21530step2 raw21530step2Labels raw21530step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4463 node4463Labels := by rfl

def raw21531 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw21531Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21531step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw21531step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21531step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw21531step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21531step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, 1, 0], ![-3, 0, 3]]
def raw21531step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw21531step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw21531step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw21531step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw21531step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21531 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21531 raw21531Labels = mixedMoment B node4266 node4266Labels := by
  calc
    mixedMoment B raw21531 raw21531Labels = mixedMoment B raw21531step0 raw21531step0Labels := by
      have hz : ∀ j, raw21531 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21531step0 = (fun i j => raw21531 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21531step0 raw21531; decide +kernel
      have hl : raw21531step0Labels = raw21531Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21531 raw21531Labels permutation434 hz
    mixedMoment B raw21531step0 raw21531step0Labels = mixedMoment B raw21531step1 raw21531step1Labels := by
      have hz : ∀ j, raw21531step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21531step1 = (fun i j => raw21531step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21531step1 raw21531step0; decide +kernel
      have hl : raw21531step1Labels = raw21531step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21531step0 raw21531step0Labels permutation80 hz
    mixedMoment B raw21531step1 raw21531step1Labels = mixedMoment B raw21531step2 raw21531step2Labels := by
      have ha : raw21531step2 = (fun i j => raw21531step1 (permutation10 i) (permutation4 j)) := by apply Matrix.ext; unfold raw21531step2 raw21531step1; decide +kernel
      have hl : raw21531step2Labels = raw21531step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21531step1 raw21531step1Labels permutation10 permutation4
    mixedMoment B raw21531step2 raw21531step2Labels = mixedMoment B raw21531step3 raw21531step3Labels := by
      have ha : raw21531step3 = -raw21531step2 := by apply Matrix.ext; change ∀ i j, raw21531step3 i j = -(raw21531step2 i j); unfold raw21531step3 raw21531step2; decide +kernel
      have hl : raw21531step3Labels = raw21531step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21531step3 raw21531step3Labels = mixedMoment B raw21531step4 raw21531step4Labels := by
      have ha : raw21531step4 = raw21531step3 := by apply Matrix.ext; unfold raw21531step4 raw21531step3; decide +kernel
      have hl : raw21531step3Labels = labelEmbedding7 ∘ raw21531step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21531step3 raw21531step3Labels raw21531step4Labels labelEmbedding7 hl
    _ = mixedMoment B node4266 node4266Labels := by rfl

def raw21532 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw21532Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21532step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw21532step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21532step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw21532step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw21532step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw21532step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21532 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21532 raw21532Labels = mixedMoment B node4398 node4398Labels := by
  calc
    mixedMoment B raw21532 raw21532Labels = mixedMoment B raw21532step0 raw21532step0Labels := by
      have hz : ∀ j, raw21532 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21532step0 = (fun i j => raw21532 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21532step0 raw21532; decide +kernel
      have hl : raw21532step0Labels = raw21532Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21532 raw21532Labels permutation434 hz
    mixedMoment B raw21532step0 raw21532step0Labels = mixedMoment B raw21532step1 raw21532step1Labels := by
      have ha : raw21532step1 = (fun i j => raw21532step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw21532step1 raw21532step0; decide +kernel
      have hl : raw21532step1Labels = raw21532step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21532step0 raw21532step0Labels permutation38 permutation6
    mixedMoment B raw21532step1 raw21532step1Labels = mixedMoment B raw21532step2 raw21532step2Labels := by
      have ha : raw21532step2 = raw21532step1 := by apply Matrix.ext; unfold raw21532step2 raw21532step1; decide +kernel
      have hl : raw21532step1Labels = labelEmbedding9 ∘ raw21532step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21532step1 raw21532step1Labels raw21532step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4398 node4398Labels := by rfl

def raw21533 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw21533Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21533step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw21533step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21533step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw21533step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21533 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21533 raw21533Labels = mixedMoment B node1215 node1215Labels := by
  calc
    mixedMoment B raw21533 raw21533Labels = mixedMoment B raw21533step0 raw21533step0Labels := by
      have hz : ∀ j, raw21533 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21533step0 = (fun i j => raw21533 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21533step0 raw21533; decide +kernel
      have hl : raw21533step0Labels = raw21533Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21533 raw21533Labels permutation434 hz
    mixedMoment B raw21533step0 raw21533step0Labels = mixedMoment B raw21533step1 raw21533step1Labels := by
      have ha : raw21533step1 = (fun i j => raw21533step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw21533step1 raw21533step0; decide +kernel
      have hl : raw21533step1Labels = raw21533step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21533step0 raw21533step0Labels permutation38 permutation6
    _ = mixedMoment B node1215 node1215Labels := by rfl

def raw21534 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw21534Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21534step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw21534step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21534step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw21534step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21534step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, -1, 0], ![3, -1, -2]]
def raw21534step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21534 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21534 raw21534Labels = mixedMoment B node826 node826Labels := by
  calc
    mixedMoment B raw21534 raw21534Labels = mixedMoment B raw21534step0 raw21534step0Labels := by
      have hz : ∀ j, raw21534 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21534step0 = (fun i j => raw21534 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21534step0 raw21534; decide +kernel
      have hl : raw21534step0Labels = raw21534Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21534 raw21534Labels permutation434 hz
    mixedMoment B raw21534step0 raw21534step0Labels = mixedMoment B raw21534step1 raw21534step1Labels := by
      have hz : ∀ j, raw21534step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21534step1 = (fun i j => raw21534step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21534step1 raw21534step0; decide +kernel
      have hl : raw21534step1Labels = raw21534step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21534step0 raw21534step0Labels permutation80 hz
    mixedMoment B raw21534step1 raw21534step1Labels = mixedMoment B raw21534step2 raw21534step2Labels := by
      have ha : raw21534step2 = (fun i j => raw21534step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw21534step2 raw21534step1; decide +kernel
      have hl : raw21534step2Labels = raw21534step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21534step1 raw21534step1Labels permutation8 permutation6
    _ = mixedMoment B node826 node826Labels := by rfl

def raw21535 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw21535Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21535step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw21535step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21535step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![3, -1, -2]]
def raw21535step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21535 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21535 raw21535Labels = mixedMoment B node989 node989Labels := by
  calc
    mixedMoment B raw21535 raw21535Labels = mixedMoment B raw21535step0 raw21535step0Labels := by
      have hz : ∀ j, raw21535 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21535step0 = (fun i j => raw21535 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21535step0 raw21535; decide +kernel
      have hl : raw21535step0Labels = raw21535Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21535 raw21535Labels permutation434 hz
    mixedMoment B raw21535step0 raw21535step0Labels = mixedMoment B raw21535step1 raw21535step1Labels := by
      have ha : raw21535step1 = (fun i j => raw21535step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw21535step1 raw21535step0; decide +kernel
      have hl : raw21535step1Labels = raw21535step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21535step0 raw21535step0Labels permutation38 permutation6
    _ = mixedMoment B node989 node989Labels := by rfl

def raw21536 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw21536Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21536step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw21536step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21536step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![3, -1, -2]]
def raw21536step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21536 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21536 raw21536Labels = mixedMoment B node989 node989Labels := by
  calc
    mixedMoment B raw21536 raw21536Labels = mixedMoment B raw21536step0 raw21536step0Labels := by
      have hz : ∀ j, raw21536 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21536step0 = (fun i j => raw21536 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21536step0 raw21536; decide +kernel
      have hl : raw21536step0Labels = raw21536Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21536 raw21536Labels permutation346 hz
    mixedMoment B raw21536step0 raw21536step0Labels = mixedMoment B raw21536step1 raw21536step1Labels := by
      have ha : raw21536step1 = (fun i j => raw21536step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw21536step1 raw21536step0; decide +kernel
      have hl : raw21536step1Labels = raw21536step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21536step0 raw21536step0Labels permutation38 permutation6
    _ = mixedMoment B node989 node989Labels := by rfl

def raw21537 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw21537Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21537step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw21537step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21537step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw21537step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21537step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -2, 1], ![3, -1, -2]]
def raw21537step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21537 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21537 raw21537Labels = mixedMoment B node1055 node1055Labels := by
  calc
    mixedMoment B raw21537 raw21537Labels = mixedMoment B raw21537step0 raw21537step0Labels := by
      have hz : ∀ j, raw21537 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21537step0 = (fun i j => raw21537 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21537step0 raw21537; decide +kernel
      have hl : raw21537step0Labels = raw21537Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21537 raw21537Labels permutation434 hz
    mixedMoment B raw21537step0 raw21537step0Labels = mixedMoment B raw21537step1 raw21537step1Labels := by
      have hz : ∀ j, raw21537step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21537step1 = (fun i j => raw21537step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21537step1 raw21537step0; decide +kernel
      have hl : raw21537step1Labels = raw21537step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21537step0 raw21537step0Labels permutation80 hz
    mixedMoment B raw21537step1 raw21537step1Labels = mixedMoment B raw21537step2 raw21537step2Labels := by
      have ha : raw21537step2 = (fun i j => raw21537step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw21537step2 raw21537step1; decide +kernel
      have hl : raw21537step2Labels = raw21537step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21537step1 raw21537step1Labels permutation8 permutation6
    _ = mixedMoment B node1055 node1055Labels := by rfl

def raw21538 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw21538Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21538step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw21538step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21538step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw21538step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21538 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21538 raw21538Labels = mixedMoment B node785 node785Labels := by
  calc
    mixedMoment B raw21538 raw21538Labels = mixedMoment B raw21538step0 raw21538step0Labels := by
      have hz : ∀ j, raw21538 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21538step0 = (fun i j => raw21538 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21538step0 raw21538; decide +kernel
      have hl : raw21538step0Labels = raw21538Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21538 raw21538Labels permutation434 hz
    mixedMoment B raw21538step0 raw21538step0Labels = mixedMoment B raw21538step1 raw21538step1Labels := by
      have ha : raw21538step1 = (fun i j => raw21538step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw21538step1 raw21538step0; decide +kernel
      have hl : raw21538step1Labels = raw21538step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21538step0 raw21538step0Labels permutation32 permutation6
    _ = mixedMoment B node785 node785Labels := by rfl

def raw21539 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw21539Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21539step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw21539step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21539step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw21539step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21539step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw21539step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21539 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21539 raw21539Labels = mixedMoment B node1043 node1043Labels := by
  calc
    mixedMoment B raw21539 raw21539Labels = mixedMoment B raw21539step0 raw21539step0Labels := by
      have hz : ∀ j, raw21539 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21539step0 = (fun i j => raw21539 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21539step0 raw21539; decide +kernel
      have hl : raw21539step0Labels = raw21539Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21539 raw21539Labels permutation434 hz
    mixedMoment B raw21539step0 raw21539step0Labels = mixedMoment B raw21539step1 raw21539step1Labels := by
      have hz : ∀ j, raw21539step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21539step1 = (fun i j => raw21539step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21539step1 raw21539step0; decide +kernel
      have hl : raw21539step1Labels = raw21539step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21539step0 raw21539step0Labels permutation56 hz
    mixedMoment B raw21539step1 raw21539step1Labels = mixedMoment B raw21539step2 raw21539step2Labels := by
      have ha : raw21539step2 = (fun i j => raw21539step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw21539step2 raw21539step1; decide +kernel
      have hl : raw21539step2Labels = raw21539step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21539step1 raw21539step1Labels permutation8 permutation6
    _ = mixedMoment B node1043 node1043Labels := by rfl

def raw21540 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw21540Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21540step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw21540step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21540 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21540 raw21540Labels = mixedMoment B node971 node971Labels := by
  calc
    mixedMoment B raw21540 raw21540Labels = mixedMoment B raw21540step0 raw21540step0Labels := by
      have ha : raw21540step0 = (fun i j => raw21540 (permutation200 i) (permutation6 j)) := by apply Matrix.ext; unfold raw21540step0 raw21540; decide +kernel
      have hl : raw21540step0Labels = raw21540Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21540 raw21540Labels permutation200 permutation6
    _ = mixedMoment B node971 node971Labels := by rfl

def raw21541 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw21541Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21541step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw21541step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21541step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw21541step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21541 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21541 raw21541Labels = mixedMoment B node1019 node1019Labels := by
  calc
    mixedMoment B raw21541 raw21541Labels = mixedMoment B raw21541step0 raw21541step0Labels := by
      have hz : ∀ j, raw21541 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21541step0 = (fun i j => raw21541 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21541step0 raw21541; decide +kernel
      have hl : raw21541step0Labels = raw21541Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21541 raw21541Labels permutation434 hz
    mixedMoment B raw21541step0 raw21541step0Labels = mixedMoment B raw21541step1 raw21541step1Labels := by
      have ha : raw21541step1 = (fun i j => raw21541step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw21541step1 raw21541step0; decide +kernel
      have hl : raw21541step1Labels = raw21541step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21541step0 raw21541step0Labels permutation32 permutation6
    _ = mixedMoment B node1019 node1019Labels := by rfl

def raw21542 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw21542Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21542step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw21542step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21542step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw21542step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21542 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21542 raw21542Labels = mixedMoment B node785 node785Labels := by
  calc
    mixedMoment B raw21542 raw21542Labels = mixedMoment B raw21542step0 raw21542step0Labels := by
      have hz : ∀ j, raw21542 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21542step0 = (fun i j => raw21542 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21542step0 raw21542; decide +kernel
      have hl : raw21542step0Labels = raw21542Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21542 raw21542Labels permutation346 hz
    mixedMoment B raw21542step0 raw21542step0Labels = mixedMoment B raw21542step1 raw21542step1Labels := by
      have ha : raw21542step1 = (fun i j => raw21542step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw21542step1 raw21542step0; decide +kernel
      have hl : raw21542step1Labels = raw21542step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21542step0 raw21542step0Labels permutation32 permutation6
    _ = mixedMoment B node785 node785Labels := by rfl

def raw21543 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw21543Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21543step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw21543step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21543step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw21543step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21543step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw21543step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21543 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21543 raw21543Labels = mixedMoment B node1043 node1043Labels := by
  calc
    mixedMoment B raw21543 raw21543Labels = mixedMoment B raw21543step0 raw21543step0Labels := by
      have hz : ∀ j, raw21543 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21543step0 = (fun i j => raw21543 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21543step0 raw21543; decide +kernel
      have hl : raw21543step0Labels = raw21543Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21543 raw21543Labels permutation346 hz
    mixedMoment B raw21543step0 raw21543step0Labels = mixedMoment B raw21543step1 raw21543step1Labels := by
      have hz : ∀ j, raw21543step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21543step1 = (fun i j => raw21543step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21543step1 raw21543step0; decide +kernel
      have hl : raw21543step1Labels = raw21543step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21543step0 raw21543step0Labels permutation56 hz
    mixedMoment B raw21543step1 raw21543step1Labels = mixedMoment B raw21543step2 raw21543step2Labels := by
      have ha : raw21543step2 = (fun i j => raw21543step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw21543step2 raw21543step1; decide +kernel
      have hl : raw21543step2Labels = raw21543step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21543step1 raw21543step1Labels permutation8 permutation6
    _ = mixedMoment B node1043 node1043Labels := by rfl

def raw21544 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw21544Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21544step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw21544step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21544 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21544 raw21544Labels = mixedMoment B node971 node971Labels := by
  calc
    mixedMoment B raw21544 raw21544Labels = mixedMoment B raw21544step0 raw21544step0Labels := by
      have ha : raw21544step0 = (fun i j => raw21544 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw21544step0 raw21544; decide +kernel
      have hl : raw21544step0Labels = raw21544Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21544 raw21544Labels permutation176 permutation6
    _ = mixedMoment B node971 node971Labels := by rfl

def raw21545 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw21545Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21545step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw21545step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21545step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw21545step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21545 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21545 raw21545Labels = mixedMoment B node1019 node1019Labels := by
  calc
    mixedMoment B raw21545 raw21545Labels = mixedMoment B raw21545step0 raw21545step0Labels := by
      have hz : ∀ j, raw21545 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21545step0 = (fun i j => raw21545 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21545step0 raw21545; decide +kernel
      have hl : raw21545step0Labels = raw21545Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21545 raw21545Labels permutation346 hz
    mixedMoment B raw21545step0 raw21545step0Labels = mixedMoment B raw21545step1 raw21545step1Labels := by
      have ha : raw21545step1 = (fun i j => raw21545step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw21545step1 raw21545step0; decide +kernel
      have hl : raw21545step1Labels = raw21545step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21545step0 raw21545step0Labels permutation32 permutation6
    _ = mixedMoment B node1019 node1019Labels := by rfl

def raw21546 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw21546Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21546step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw21546step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21546step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw21546step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21546step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21546step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21546 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21546 raw21546Labels = mixedMoment B node1046 node1046Labels := by
  calc
    mixedMoment B raw21546 raw21546Labels = mixedMoment B raw21546step0 raw21546step0Labels := by
      have hz : ∀ j, raw21546 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21546step0 = (fun i j => raw21546 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21546step0 raw21546; decide +kernel
      have hl : raw21546step0Labels = raw21546Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21546 raw21546Labels permutation434 hz
    mixedMoment B raw21546step0 raw21546step0Labels = mixedMoment B raw21546step1 raw21546step1Labels := by
      have hz : ∀ j, raw21546step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21546step1 = (fun i j => raw21546step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21546step1 raw21546step0; decide +kernel
      have hl : raw21546step1Labels = raw21546step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21546step0 raw21546step0Labels permutation80 hz
    mixedMoment B raw21546step1 raw21546step1Labels = mixedMoment B raw21546step2 raw21546step2Labels := by
      have ha : raw21546step2 = (fun i j => raw21546step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw21546step2 raw21546step1; decide +kernel
      have hl : raw21546step2Labels = raw21546step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21546step1 raw21546step1Labels permutation8 permutation6
    _ = mixedMoment B node1046 node1046Labels := by rfl

def raw21547 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw21547Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21547step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw21547step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21547step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw21547step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21547step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw21547step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21547 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21547 raw21547Labels = mixedMoment B node809 node809Labels := by
  calc
    mixedMoment B raw21547 raw21547Labels = mixedMoment B raw21547step0 raw21547step0Labels := by
      have hz : ∀ j, raw21547 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21547step0 = (fun i j => raw21547 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21547step0 raw21547; decide +kernel
      have hl : raw21547step0Labels = raw21547Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21547 raw21547Labels permutation434 hz
    mixedMoment B raw21547step0 raw21547step0Labels = mixedMoment B raw21547step1 raw21547step1Labels := by
      have hz : ∀ j, raw21547step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21547step1 = (fun i j => raw21547step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21547step1 raw21547step0; decide +kernel
      have hl : raw21547step1Labels = raw21547step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21547step0 raw21547step0Labels permutation80 hz
    mixedMoment B raw21547step1 raw21547step1Labels = mixedMoment B raw21547step2 raw21547step2Labels := by
      have ha : raw21547step2 = (fun i j => raw21547step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw21547step2 raw21547step1; decide +kernel
      have hl : raw21547step2Labels = raw21547step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21547step1 raw21547step1Labels permutation8 permutation6
    _ = mixedMoment B node809 node809Labels := by rfl

def raw21548 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw21548Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21548step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw21548step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21548step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw21548step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21548 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21548 raw21548Labels = mixedMoment B node979 node979Labels := by
  calc
    mixedMoment B raw21548 raw21548Labels = mixedMoment B raw21548step0 raw21548step0Labels := by
      have hz : ∀ j, raw21548 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21548step0 = (fun i j => raw21548 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21548step0 raw21548; decide +kernel
      have hl : raw21548step0Labels = raw21548Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21548 raw21548Labels permutation434 hz
    mixedMoment B raw21548step0 raw21548step0Labels = mixedMoment B raw21548step1 raw21548step1Labels := by
      have ha : raw21548step1 = (fun i j => raw21548step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw21548step1 raw21548step0; decide +kernel
      have hl : raw21548step1Labels = raw21548step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21548step0 raw21548step0Labels permutation38 permutation6
    _ = mixedMoment B node979 node979Labels := by rfl

def raw21549 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw21549Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21549step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw21549step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21549step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw21549step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21549 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21549 raw21549Labels = mixedMoment B node979 node979Labels := by
  calc
    mixedMoment B raw21549 raw21549Labels = mixedMoment B raw21549step0 raw21549step0Labels := by
      have hz : ∀ j, raw21549 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21549step0 = (fun i j => raw21549 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21549step0 raw21549; decide +kernel
      have hl : raw21549step0Labels = raw21549Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21549 raw21549Labels permutation346 hz
    mixedMoment B raw21549step0 raw21549step0Labels = mixedMoment B raw21549step1 raw21549step1Labels := by
      have ha : raw21549step1 = (fun i j => raw21549step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw21549step1 raw21549step0; decide +kernel
      have hl : raw21549step1Labels = raw21549step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21549step0 raw21549step0Labels permutation38 permutation6
    _ = mixedMoment B node979 node979Labels := by rfl

def raw21550 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw21550Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21550step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw21550step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21550step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw21550step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21550step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![1, 0, -1], ![3, -2, -1]]
def raw21550step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21550step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![1, 0, -1], ![3, -2, -1]]
def raw21550step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21550 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21550 raw21550Labels = mixedMoment B node1471 node1471Labels := by
  calc
    mixedMoment B raw21550 raw21550Labels = mixedMoment B raw21550step0 raw21550step0Labels := by
      have hz : ∀ j, raw21550 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21550step0 = (fun i j => raw21550 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21550step0 raw21550; decide +kernel
      have hl : raw21550step0Labels = raw21550Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21550 raw21550Labels permutation434 hz
    mixedMoment B raw21550step0 raw21550step0Labels = mixedMoment B raw21550step1 raw21550step1Labels := by
      have hz : ∀ j, raw21550step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21550step1 = (fun i j => raw21550step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21550step1 raw21550step0; decide +kernel
      have hl : raw21550step1Labels = raw21550step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21550step0 raw21550step0Labels permutation80 hz
    mixedMoment B raw21550step1 raw21550step1Labels = mixedMoment B raw21550step2 raw21550step2Labels := by
      have ha : raw21550step2 = (fun i j => raw21550step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21550step2 raw21550step1; decide +kernel
      have hl : raw21550step2Labels = raw21550step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21550step1 raw21550step1Labels permutation8 permutation7
    mixedMoment B raw21550step2 raw21550step2Labels = mixedMoment B raw21550step3 raw21550step3Labels := by
      have ha : raw21550step3 = raw21550step2 := by apply Matrix.ext; unfold raw21550step3 raw21550step2; decide +kernel
      have hl : raw21550step2Labels = labelEmbedding1 ∘ raw21550step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21550step2 raw21550step2Labels raw21550step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1471 node1471Labels := by rfl

def raw21551 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw21551Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21551step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw21551step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21551step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21551step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21551step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21551step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21551 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21551 raw21551Labels = mixedMoment B node1361 node1361Labels := by
  calc
    mixedMoment B raw21551 raw21551Labels = mixedMoment B raw21551step0 raw21551step0Labels := by
      have hz : ∀ j, raw21551 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21551step0 = (fun i j => raw21551 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21551step0 raw21551; decide +kernel
      have hl : raw21551step0Labels = raw21551Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21551 raw21551Labels permutation434 hz
    mixedMoment B raw21551step0 raw21551step0Labels = mixedMoment B raw21551step1 raw21551step1Labels := by
      have ha : raw21551step1 = (fun i j => raw21551step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21551step1 raw21551step0; decide +kernel
      have hl : raw21551step1Labels = raw21551step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21551step0 raw21551step0Labels permutation32 permutation7
    mixedMoment B raw21551step1 raw21551step1Labels = mixedMoment B raw21551step2 raw21551step2Labels := by
      have ha : raw21551step2 = raw21551step1 := by apply Matrix.ext; unfold raw21551step2 raw21551step1; decide +kernel
      have hl : raw21551step1Labels = labelEmbedding1 ∘ raw21551step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21551step1 raw21551step1Labels raw21551step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1361 node1361Labels := by rfl

def raw21552 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw21552Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21552step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw21552step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21552step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21552step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21552step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21552step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21552 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21552 raw21552Labels = mixedMoment B node1361 node1361Labels := by
  calc
    mixedMoment B raw21552 raw21552Labels = mixedMoment B raw21552step0 raw21552step0Labels := by
      have hz : ∀ j, raw21552 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21552step0 = (fun i j => raw21552 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21552step0 raw21552; decide +kernel
      have hl : raw21552step0Labels = raw21552Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21552 raw21552Labels permutation346 hz
    mixedMoment B raw21552step0 raw21552step0Labels = mixedMoment B raw21552step1 raw21552step1Labels := by
      have ha : raw21552step1 = (fun i j => raw21552step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21552step1 raw21552step0; decide +kernel
      have hl : raw21552step1Labels = raw21552step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21552step0 raw21552step0Labels permutation32 permutation7
    mixedMoment B raw21552step1 raw21552step1Labels = mixedMoment B raw21552step2 raw21552step2Labels := by
      have ha : raw21552step2 = raw21552step1 := by apply Matrix.ext; unfold raw21552step2 raw21552step1; decide +kernel
      have hl : raw21552step1Labels = labelEmbedding1 ∘ raw21552step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21552step1 raw21552step1Labels raw21552step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1361 node1361Labels := by rfl

def raw21553 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw21553Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21553step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw21553step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21553step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw21553step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21553step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, 1, -2], ![3, -2, -1]]
def raw21553step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21553step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, 1, -2], ![3, -2, -1]]
def raw21553step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21553 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21553 raw21553Labels = mixedMoment B node1373 node1373Labels := by
  calc
    mixedMoment B raw21553 raw21553Labels = mixedMoment B raw21553step0 raw21553step0Labels := by
      have hz : ∀ j, raw21553 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21553step0 = (fun i j => raw21553 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21553step0 raw21553; decide +kernel
      have hl : raw21553step0Labels = raw21553Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21553 raw21553Labels permutation434 hz
    mixedMoment B raw21553step0 raw21553step0Labels = mixedMoment B raw21553step1 raw21553step1Labels := by
      have hz : ∀ j, raw21553step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21553step1 = (fun i j => raw21553step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21553step1 raw21553step0; decide +kernel
      have hl : raw21553step1Labels = raw21553step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21553step0 raw21553step0Labels permutation80 hz
    mixedMoment B raw21553step1 raw21553step1Labels = mixedMoment B raw21553step2 raw21553step2Labels := by
      have ha : raw21553step2 = (fun i j => raw21553step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21553step2 raw21553step1; decide +kernel
      have hl : raw21553step2Labels = raw21553step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21553step1 raw21553step1Labels permutation8 permutation7
    mixedMoment B raw21553step2 raw21553step2Labels = mixedMoment B raw21553step3 raw21553step3Labels := by
      have ha : raw21553step3 = raw21553step2 := by apply Matrix.ext; unfold raw21553step3 raw21553step2; decide +kernel
      have hl : raw21553step2Labels = labelEmbedding1 ∘ raw21553step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21553step2 raw21553step2Labels raw21553step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1373 node1373Labels := by rfl

def raw21554 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw21554Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21554step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw21554step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21554step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw21554step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21554step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw21554step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21554 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21554 raw21554Labels = mixedMoment B node1478 node1478Labels := by
  calc
    mixedMoment B raw21554 raw21554Labels = mixedMoment B raw21554step0 raw21554step0Labels := by
      have hz : ∀ j, raw21554 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21554step0 = (fun i j => raw21554 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21554step0 raw21554; decide +kernel
      have hl : raw21554step0Labels = raw21554Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21554 raw21554Labels permutation434 hz
    mixedMoment B raw21554step0 raw21554step0Labels = mixedMoment B raw21554step1 raw21554step1Labels := by
      have ha : raw21554step1 = (fun i j => raw21554step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21554step1 raw21554step0; decide +kernel
      have hl : raw21554step1Labels = raw21554step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21554step0 raw21554step0Labels permutation32 permutation7
    mixedMoment B raw21554step1 raw21554step1Labels = mixedMoment B raw21554step2 raw21554step2Labels := by
      have ha : raw21554step2 = raw21554step1 := by apply Matrix.ext; unfold raw21554step2 raw21554step1; decide +kernel
      have hl : raw21554step1Labels = labelEmbedding1 ∘ raw21554step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21554step1 raw21554step1Labels raw21554step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1478 node1478Labels := by rfl

def raw21555 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw21555Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21555step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21555step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21555step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21555step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21555 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21555 raw21555Labels = mixedMoment B node1379 node1379Labels := by
  calc
    mixedMoment B raw21555 raw21555Labels = mixedMoment B raw21555step0 raw21555step0Labels := by
      have ha : raw21555step0 = (fun i j => raw21555 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21555step0 raw21555; decide +kernel
      have hl : raw21555step0Labels = raw21555Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21555 raw21555Labels permutation152 permutation7
    mixedMoment B raw21555step0 raw21555step0Labels = mixedMoment B raw21555step1 raw21555step1Labels := by
      have ha : raw21555step1 = raw21555step0 := by apply Matrix.ext; unfold raw21555step1 raw21555step0; decide +kernel
      have hl : raw21555step0Labels = labelEmbedding1 ∘ raw21555step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21555step0 raw21555step0Labels raw21555step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1379 node1379Labels := by rfl

def raw21556 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw21556Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21556step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw21556step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21556step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw21556step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21556step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw21556step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21556 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21556 raw21556Labels = mixedMoment B node1389 node1389Labels := by
  calc
    mixedMoment B raw21556 raw21556Labels = mixedMoment B raw21556step0 raw21556step0Labels := by
      have hz : ∀ j, raw21556 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21556step0 = (fun i j => raw21556 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21556step0 raw21556; decide +kernel
      have hl : raw21556step0Labels = raw21556Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21556 raw21556Labels permutation434 hz
    mixedMoment B raw21556step0 raw21556step0Labels = mixedMoment B raw21556step1 raw21556step1Labels := by
      have ha : raw21556step1 = (fun i j => raw21556step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21556step1 raw21556step0; decide +kernel
      have hl : raw21556step1Labels = raw21556step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21556step0 raw21556step0Labels permutation32 permutation7
    mixedMoment B raw21556step1 raw21556step1Labels = mixedMoment B raw21556step2 raw21556step2Labels := by
      have ha : raw21556step2 = raw21556step1 := by apply Matrix.ext; unfold raw21556step2 raw21556step1; decide +kernel
      have hl : raw21556step1Labels = labelEmbedding1 ∘ raw21556step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21556step1 raw21556step1Labels raw21556step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1389 node1389Labels := by rfl

def raw21557 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw21557Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21557step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw21557step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21557step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw21557step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21557step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw21557step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21557 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21557 raw21557Labels = mixedMoment B node1478 node1478Labels := by
  calc
    mixedMoment B raw21557 raw21557Labels = mixedMoment B raw21557step0 raw21557step0Labels := by
      have hz : ∀ j, raw21557 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21557step0 = (fun i j => raw21557 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21557step0 raw21557; decide +kernel
      have hl : raw21557step0Labels = raw21557Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21557 raw21557Labels permutation346 hz
    mixedMoment B raw21557step0 raw21557step0Labels = mixedMoment B raw21557step1 raw21557step1Labels := by
      have ha : raw21557step1 = (fun i j => raw21557step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21557step1 raw21557step0; decide +kernel
      have hl : raw21557step1Labels = raw21557step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21557step0 raw21557step0Labels permutation32 permutation7
    mixedMoment B raw21557step1 raw21557step1Labels = mixedMoment B raw21557step2 raw21557step2Labels := by
      have ha : raw21557step2 = raw21557step1 := by apply Matrix.ext; unfold raw21557step2 raw21557step1; decide +kernel
      have hl : raw21557step1Labels = labelEmbedding1 ∘ raw21557step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21557step1 raw21557step1Labels raw21557step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1478 node1478Labels := by rfl

def raw21558 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw21558Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21558step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21558step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21558step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21558step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21558 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21558 raw21558Labels = mixedMoment B node1379 node1379Labels := by
  calc
    mixedMoment B raw21558 raw21558Labels = mixedMoment B raw21558step0 raw21558step0Labels := by
      have ha : raw21558step0 = (fun i j => raw21558 (permutation158 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21558step0 raw21558; decide +kernel
      have hl : raw21558step0Labels = raw21558Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21558 raw21558Labels permutation158 permutation7
    mixedMoment B raw21558step0 raw21558step0Labels = mixedMoment B raw21558step1 raw21558step1Labels := by
      have ha : raw21558step1 = raw21558step0 := by apply Matrix.ext; unfold raw21558step1 raw21558step0; decide +kernel
      have hl : raw21558step0Labels = labelEmbedding1 ∘ raw21558step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21558step0 raw21558step0Labels raw21558step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1379 node1379Labels := by rfl

def raw21559 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw21559Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21559step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw21559step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21559step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw21559step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21559step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw21559step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21559 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21559 raw21559Labels = mixedMoment B node1389 node1389Labels := by
  calc
    mixedMoment B raw21559 raw21559Labels = mixedMoment B raw21559step0 raw21559step0Labels := by
      have hz : ∀ j, raw21559 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21559step0 = (fun i j => raw21559 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21559step0 raw21559; decide +kernel
      have hl : raw21559step0Labels = raw21559Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21559 raw21559Labels permutation346 hz
    mixedMoment B raw21559step0 raw21559step0Labels = mixedMoment B raw21559step1 raw21559step1Labels := by
      have ha : raw21559step1 = (fun i j => raw21559step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21559step1 raw21559step0; decide +kernel
      have hl : raw21559step1Labels = raw21559step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21559step0 raw21559step0Labels permutation32 permutation7
    mixedMoment B raw21559step1 raw21559step1Labels = mixedMoment B raw21559step2 raw21559step2Labels := by
      have ha : raw21559step2 = raw21559step1 := by apply Matrix.ext; unfold raw21559step2 raw21559step1; decide +kernel
      have hl : raw21559step1Labels = labelEmbedding1 ∘ raw21559step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21559step1 raw21559step1Labels raw21559step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1389 node1389Labels := by rfl

def raw21560 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw21560Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21560step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw21560step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21560step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw21560step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21560step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw21560step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21560step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw21560step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21560 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21560 raw21560Labels = mixedMoment B node1413 node1413Labels := by
  calc
    mixedMoment B raw21560 raw21560Labels = mixedMoment B raw21560step0 raw21560step0Labels := by
      have hz : ∀ j, raw21560 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21560step0 = (fun i j => raw21560 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21560step0 raw21560; decide +kernel
      have hl : raw21560step0Labels = raw21560Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21560 raw21560Labels permutation434 hz
    mixedMoment B raw21560step0 raw21560step0Labels = mixedMoment B raw21560step1 raw21560step1Labels := by
      have hz : ∀ j, raw21560step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21560step1 = (fun i j => raw21560step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21560step1 raw21560step0; decide +kernel
      have hl : raw21560step1Labels = raw21560step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21560step0 raw21560step0Labels permutation80 hz
    mixedMoment B raw21560step1 raw21560step1Labels = mixedMoment B raw21560step2 raw21560step2Labels := by
      have ha : raw21560step2 = (fun i j => raw21560step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21560step2 raw21560step1; decide +kernel
      have hl : raw21560step2Labels = raw21560step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21560step1 raw21560step1Labels permutation8 permutation7
    mixedMoment B raw21560step2 raw21560step2Labels = mixedMoment B raw21560step3 raw21560step3Labels := by
      have ha : raw21560step3 = raw21560step2 := by apply Matrix.ext; unfold raw21560step3 raw21560step2; decide +kernel
      have hl : raw21560step2Labels = labelEmbedding1 ∘ raw21560step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21560step2 raw21560step2Labels raw21560step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1413 node1413Labels := by rfl

def raw21561 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw21561Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21561step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw21561step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21561step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw21561step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21561step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -4, 0], ![0, 1, -1], ![-1, 0, 1], ![-3, 3, 0]]
def raw21561step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21561step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![1, 0, -1], ![3, -3, 0]]
def raw21561step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21561step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![1, 0, -1], ![3, -3, 0]]
def raw21561step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21561 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21561 raw21561Labels = mixedMoment B node1485 node1485Labels := by
  calc
    mixedMoment B raw21561 raw21561Labels = mixedMoment B raw21561step0 raw21561step0Labels := by
      have hz : ∀ j, raw21561 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21561step0 = (fun i j => raw21561 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21561step0 raw21561; decide +kernel
      have hl : raw21561step0Labels = raw21561Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21561 raw21561Labels permutation434 hz
    mixedMoment B raw21561step0 raw21561step0Labels = mixedMoment B raw21561step1 raw21561step1Labels := by
      have hz : ∀ j, raw21561step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21561step1 = (fun i j => raw21561step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21561step1 raw21561step0; decide +kernel
      have hl : raw21561step1Labels = raw21561step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21561step0 raw21561step0Labels permutation80 hz
    mixedMoment B raw21561step1 raw21561step1Labels = mixedMoment B raw21561step2 raw21561step2Labels := by
      have ha : raw21561step2 = (fun i j => raw21561step1 (permutation10 i) (permutation5 j)) := by apply Matrix.ext; unfold raw21561step2 raw21561step1; decide +kernel
      have hl : raw21561step2Labels = raw21561step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21561step1 raw21561step1Labels permutation10 permutation5
    mixedMoment B raw21561step2 raw21561step2Labels = mixedMoment B raw21561step3 raw21561step3Labels := by
      have ha : raw21561step3 = -raw21561step2 := by apply Matrix.ext; change ∀ i j, raw21561step3 i j = -(raw21561step2 i j); unfold raw21561step3 raw21561step2; decide +kernel
      have hl : raw21561step3Labels = raw21561step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21561step3 raw21561step3Labels = mixedMoment B raw21561step4 raw21561step4Labels := by
      have ha : raw21561step4 = raw21561step3 := by apply Matrix.ext; unfold raw21561step4 raw21561step3; decide +kernel
      have hl : raw21561step3Labels = labelEmbedding1 ∘ raw21561step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21561step3 raw21561step3Labels raw21561step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1485 node1485Labels := by rfl

def raw21562 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw21562Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21562step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw21562step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21562step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw21562step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21562step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw21562step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21562 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21562 raw21562Labels = mixedMoment B node1399 node1399Labels := by
  calc
    mixedMoment B raw21562 raw21562Labels = mixedMoment B raw21562step0 raw21562step0Labels := by
      have hz : ∀ j, raw21562 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21562step0 = (fun i j => raw21562 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21562step0 raw21562; decide +kernel
      have hl : raw21562step0Labels = raw21562Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21562 raw21562Labels permutation434 hz
    mixedMoment B raw21562step0 raw21562step0Labels = mixedMoment B raw21562step1 raw21562step1Labels := by
      have ha : raw21562step1 = (fun i j => raw21562step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21562step1 raw21562step0; decide +kernel
      have hl : raw21562step1Labels = raw21562step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21562step0 raw21562step0Labels permutation32 permutation7
    mixedMoment B raw21562step1 raw21562step1Labels = mixedMoment B raw21562step2 raw21562step2Labels := by
      have ha : raw21562step2 = raw21562step1 := by apply Matrix.ext; unfold raw21562step2 raw21562step1; decide +kernel
      have hl : raw21562step1Labels = labelEmbedding1 ∘ raw21562step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21562step1 raw21562step1Labels raw21562step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1399 node1399Labels := by rfl

def raw21563 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw21563Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21563step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw21563step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21563step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw21563step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21563 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21563 raw21563Labels = mixedMoment B node1037 node1037Labels := by
  calc
    mixedMoment B raw21563 raw21563Labels = mixedMoment B raw21563step0 raw21563step0Labels := by
      have hz : ∀ j, raw21563 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21563step0 = (fun i j => raw21563 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21563step0 raw21563; decide +kernel
      have hl : raw21563step0Labels = raw21563Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21563 raw21563Labels permutation434 hz
    mixedMoment B raw21563step0 raw21563step0Labels = mixedMoment B raw21563step1 raw21563step1Labels := by
      have hz : ∀ j, raw21563step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21563step1 = (fun i j => raw21563step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21563step1 raw21563step0; decide +kernel
      have hl : raw21563step1Labels = raw21563step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21563step0 raw21563step0Labels permutation80 hz
    _ = mixedMoment B node1037 node1037Labels := by rfl

def raw21564 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw21564Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21564step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw21564step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21564step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![3, 0, -3]]
def raw21564step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21564 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21564 raw21564Labels = mixedMoment B node2103 node2103Labels := by
  calc
    mixedMoment B raw21564 raw21564Labels = mixedMoment B raw21564step0 raw21564step0Labels := by
      have hz : ∀ j, raw21564 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21564step0 = (fun i j => raw21564 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21564step0 raw21564; decide +kernel
      have hl : raw21564step0Labels = raw21564Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21564 raw21564Labels permutation434 hz
    mixedMoment B raw21564step0 raw21564step0Labels = mixedMoment B raw21564step1 raw21564step1Labels := by
      have hz : ∀ j, raw21564step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21564step1 = (fun i j => raw21564step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21564step1 raw21564step0; decide +kernel
      have hl : raw21564step1Labels = raw21564step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21564step0 raw21564step0Labels permutation80 hz
    _ = mixedMoment B node2103 node2103Labels := by rfl

def raw21565 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw21565Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21565step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw21565step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21565step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw21565step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21565 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21565 raw21565Labels = mixedMoment B node2018 node2018Labels := by
  calc
    mixedMoment B raw21565 raw21565Labels = mixedMoment B raw21565step0 raw21565step0Labels := by
      have hz : ∀ j, raw21565 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21565step0 = (fun i j => raw21565 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21565step0 raw21565; decide +kernel
      have hl : raw21565step0Labels = raw21565Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21565 raw21565Labels permutation434 hz
    mixedMoment B raw21565step0 raw21565step0Labels = mixedMoment B raw21565step1 raw21565step1Labels := by
      have ha : raw21565step1 = (fun i j => raw21565step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21565step1 raw21565step0; decide +kernel
      have hl : raw21565step1Labels = raw21565step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21565step0 raw21565step0Labels permutation38 permutation2
    _ = mixedMoment B node2018 node2018Labels := by rfl

def raw21566 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw21566Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21566step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw21566step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21566step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw21566step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21566 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21566 raw21566Labels = mixedMoment B node2018 node2018Labels := by
  calc
    mixedMoment B raw21566 raw21566Labels = mixedMoment B raw21566step0 raw21566step0Labels := by
      have hz : ∀ j, raw21566 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21566step0 = (fun i j => raw21566 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21566step0 raw21566; decide +kernel
      have hl : raw21566step0Labels = raw21566Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21566 raw21566Labels permutation346 hz
    mixedMoment B raw21566step0 raw21566step0Labels = mixedMoment B raw21566step1 raw21566step1Labels := by
      have ha : raw21566step1 = (fun i j => raw21566step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21566step1 raw21566step0; decide +kernel
      have hl : raw21566step1Labels = raw21566step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21566step0 raw21566step0Labels permutation38 permutation2
    _ = mixedMoment B node2018 node2018Labels := by rfl

def raw21567 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw21567Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21567step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw21567step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21567step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw21567step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21567 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21567 raw21567Labels = mixedMoment B node2261 node2261Labels := by
  calc
    mixedMoment B raw21567 raw21567Labels = mixedMoment B raw21567step0 raw21567step0Labels := by
      have hz : ∀ j, raw21567 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21567step0 = (fun i j => raw21567 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21567step0 raw21567; decide +kernel
      have hl : raw21567step0Labels = raw21567Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21567 raw21567Labels permutation434 hz
    mixedMoment B raw21567step0 raw21567step0Labels = mixedMoment B raw21567step1 raw21567step1Labels := by
      have hz : ∀ j, raw21567step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21567step1 = (fun i j => raw21567step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21567step1 raw21567step0; decide +kernel
      have hl : raw21567step1Labels = raw21567step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21567step0 raw21567step0Labels permutation80 hz
    _ = mixedMoment B node2261 node2261Labels := by rfl

def raw21568 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw21568Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21568step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw21568step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21568step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, -2, 1], ![3, 0, -3]]
def raw21568step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21568step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21568step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21568 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21568 raw21568Labels = mixedMoment B node594 node594Labels := by
  calc
    mixedMoment B raw21568 raw21568Labels = mixedMoment B raw21568step0 raw21568step0Labels := by
      have hz : ∀ j, raw21568 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21568step0 = (fun i j => raw21568 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21568step0 raw21568; decide +kernel
      have hl : raw21568step0Labels = raw21568Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21568 raw21568Labels permutation434 hz
    mixedMoment B raw21568step0 raw21568step0Labels = mixedMoment B raw21568step1 raw21568step1Labels := by
      have hz : ∀ j, raw21568step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21568step1 = (fun i j => raw21568step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21568step1 raw21568step0; decide +kernel
      have hl : raw21568step1Labels = raw21568step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21568step0 raw21568step0Labels permutation80 hz
    mixedMoment B raw21568step1 raw21568step1Labels = mixedMoment B raw21568step2 raw21568step2Labels := by
      have ha : raw21568step2 = (fun i j => raw21568step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21568step2 raw21568step1; decide +kernel
      have hl : raw21568step2Labels = raw21568step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21568step1 raw21568step1Labels permutation10 permutation2
    _ = mixedMoment B node594 node594Labels := by rfl

def raw21569 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw21569Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21569step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw21569step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21569step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21569step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21569 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21569 raw21569Labels = mixedMoment B node916 node916Labels := by
  calc
    mixedMoment B raw21569 raw21569Labels = mixedMoment B raw21569step0 raw21569step0Labels := by
      have hz : ∀ j, raw21569 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21569step0 = (fun i j => raw21569 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21569step0 raw21569; decide +kernel
      have hl : raw21569step0Labels = raw21569Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21569 raw21569Labels permutation434 hz
    mixedMoment B raw21569step0 raw21569step0Labels = mixedMoment B raw21569step1 raw21569step1Labels := by
      have ha : raw21569step1 = (fun i j => raw21569step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21569step1 raw21569step0; decide +kernel
      have hl : raw21569step1Labels = raw21569step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21569step0 raw21569step0Labels permutation40 permutation2
    _ = mixedMoment B node916 node916Labels := by rfl

def raw21570 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw21570Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21570step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw21570step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21570step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21570step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21570 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21570 raw21570Labels = mixedMoment B node916 node916Labels := by
  calc
    mixedMoment B raw21570 raw21570Labels = mixedMoment B raw21570step0 raw21570step0Labels := by
      have hz : ∀ j, raw21570 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21570step0 = (fun i j => raw21570 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21570step0 raw21570; decide +kernel
      have hl : raw21570step0Labels = raw21570Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21570 raw21570Labels permutation346 hz
    mixedMoment B raw21570step0 raw21570step0Labels = mixedMoment B raw21570step1 raw21570step1Labels := by
      have ha : raw21570step1 = (fun i j => raw21570step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21570step1 raw21570step0; decide +kernel
      have hl : raw21570step1Labels = raw21570step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21570step0 raw21570step0Labels permutation40 permutation2
    _ = mixedMoment B node916 node916Labels := by rfl

def raw21571 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw21571Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21571step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw21571step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21571step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, -2, 1], ![2, 1, -3]]
def raw21571step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21571step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw21571step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21571 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21571 raw21571Labels = mixedMoment B node1074 node1074Labels := by
  calc
    mixedMoment B raw21571 raw21571Labels = mixedMoment B raw21571step0 raw21571step0Labels := by
      have hz : ∀ j, raw21571 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21571step0 = (fun i j => raw21571 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21571step0 raw21571; decide +kernel
      have hl : raw21571step0Labels = raw21571Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21571 raw21571Labels permutation434 hz
    mixedMoment B raw21571step0 raw21571step0Labels = mixedMoment B raw21571step1 raw21571step1Labels := by
      have hz : ∀ j, raw21571step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21571step1 = (fun i j => raw21571step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21571step1 raw21571step0; decide +kernel
      have hl : raw21571step1Labels = raw21571step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21571step0 raw21571step0Labels permutation80 hz
    mixedMoment B raw21571step1 raw21571step1Labels = mixedMoment B raw21571step2 raw21571step2Labels := by
      have ha : raw21571step2 = (fun i j => raw21571step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21571step2 raw21571step1; decide +kernel
      have hl : raw21571step2Labels = raw21571step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21571step1 raw21571step1Labels permutation10 permutation2
    _ = mixedMoment B node1074 node1074Labels := by rfl

def raw21572 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw21572Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21572step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw21572step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21572step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw21572step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21572 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21572 raw21572Labels = mixedMoment B node1033 node1033Labels := by
  calc
    mixedMoment B raw21572 raw21572Labels = mixedMoment B raw21572step0 raw21572step0Labels := by
      have hz : ∀ j, raw21572 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21572step0 = (fun i j => raw21572 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21572step0 raw21572; decide +kernel
      have hl : raw21572step0Labels = raw21572Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21572 raw21572Labels permutation434 hz
    mixedMoment B raw21572step0 raw21572step0Labels = mixedMoment B raw21572step1 raw21572step1Labels := by
      have ha : raw21572step1 = (fun i j => raw21572step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21572step1 raw21572step0; decide +kernel
      have hl : raw21572step1Labels = raw21572step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21572step0 raw21572step0Labels permutation34 permutation2
    _ = mixedMoment B node1033 node1033Labels := by rfl

def raw21573 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw21573Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21573step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw21573step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21573step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw21573step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21573 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21573 raw21573Labels = mixedMoment B node1033 node1033Labels := by
  calc
    mixedMoment B raw21573 raw21573Labels = mixedMoment B raw21573step0 raw21573step0Labels := by
      have hz : ∀ j, raw21573 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21573step0 = (fun i j => raw21573 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21573step0 raw21573; decide +kernel
      have hl : raw21573step0Labels = raw21573Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21573 raw21573Labels permutation346 hz
    mixedMoment B raw21573step0 raw21573step0Labels = mixedMoment B raw21573step1 raw21573step1Labels := by
      have ha : raw21573step1 = (fun i j => raw21573step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21573step1 raw21573step0; decide +kernel
      have hl : raw21573step1Labels = raw21573step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21573step0 raw21573step0Labels permutation34 permutation2
    _ = mixedMoment B node1033 node1033Labels := by rfl

def raw21574 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![2, 1, -3]]
def raw21574Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21574step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![2, -3, 1], ![2, 1, -3]]
def raw21574step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21574step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -3, 1], ![2, 1, -3]]
def raw21574step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21574 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21574 raw21574Labels = mixedMoment B node1048 node1048Labels := by
  calc
    mixedMoment B raw21574 raw21574Labels = mixedMoment B raw21574step0 raw21574step0Labels := by
      have hz : ∀ j, raw21574 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21574step0 = (fun i j => raw21574 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21574step0 raw21574; decide +kernel
      have hl : raw21574step0Labels = raw21574Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21574 raw21574Labels permutation434 hz
    mixedMoment B raw21574step0 raw21574step0Labels = mixedMoment B raw21574step1 raw21574step1Labels := by
      have hz : ∀ j, raw21574step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21574step1 = (fun i j => raw21574step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21574step1 raw21574step0; decide +kernel
      have hl : raw21574step1Labels = raw21574step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21574step0 raw21574step0Labels permutation80 hz
    _ = mixedMoment B node1048 node1048Labels := by rfl

def raw21575 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw21575Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21575step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw21575step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21575step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw21575step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21575step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![1, -2, 1], ![-2, 2, 0], ![-3, 0, 3]]
def raw21575step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21575step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![2, -2, 0], ![3, 0, -3]]
def raw21575step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21575 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21575 raw21575Labels = mixedMoment B node741 node741Labels := by
  calc
    mixedMoment B raw21575 raw21575Labels = mixedMoment B raw21575step0 raw21575step0Labels := by
      have hz : ∀ j, raw21575 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21575step0 = (fun i j => raw21575 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21575step0 raw21575; decide +kernel
      have hl : raw21575step0Labels = raw21575Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21575 raw21575Labels permutation434 hz
    mixedMoment B raw21575step0 raw21575step0Labels = mixedMoment B raw21575step1 raw21575step1Labels := by
      have hz : ∀ j, raw21575step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21575step1 = (fun i j => raw21575step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21575step1 raw21575step0; decide +kernel
      have hl : raw21575step1Labels = raw21575step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21575step0 raw21575step0Labels permutation80 hz
    mixedMoment B raw21575step1 raw21575step1Labels = mixedMoment B raw21575step2 raw21575step2Labels := by
      have ha : raw21575step2 = (fun i j => raw21575step1 (permutation10 i) (permutation4 j)) := by apply Matrix.ext; unfold raw21575step2 raw21575step1; decide +kernel
      have hl : raw21575step2Labels = raw21575step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21575step1 raw21575step1Labels permutation10 permutation4
    mixedMoment B raw21575step2 raw21575step2Labels = mixedMoment B raw21575step3 raw21575step3Labels := by
      have ha : raw21575step3 = -raw21575step2 := by apply Matrix.ext; change ∀ i j, raw21575step3 i j = -(raw21575step2 i j); unfold raw21575step3 raw21575step2; decide +kernel
      have hl : raw21575step3Labels = raw21575step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node741 node741Labels := by rfl

def raw21576 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw21576Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21576step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw21576step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21576step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-3, 0, 3]]
def raw21576step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21576step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21576step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21576 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21576 raw21576Labels = mixedMoment B node731 node731Labels := by
  calc
    mixedMoment B raw21576 raw21576Labels = mixedMoment B raw21576step0 raw21576step0Labels := by
      have hz : ∀ j, raw21576 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21576step0 = (fun i j => raw21576 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21576step0 raw21576; decide +kernel
      have hl : raw21576step0Labels = raw21576Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21576 raw21576Labels permutation434 hz
    mixedMoment B raw21576step0 raw21576step0Labels = mixedMoment B raw21576step1 raw21576step1Labels := by
      have ha : raw21576step1 = (fun i j => raw21576step0 (permutation44 i) (permutation4 j)) := by apply Matrix.ext; unfold raw21576step1 raw21576step0; decide +kernel
      have hl : raw21576step1Labels = raw21576step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21576step0 raw21576step0Labels permutation44 permutation4
    mixedMoment B raw21576step1 raw21576step1Labels = mixedMoment B raw21576step2 raw21576step2Labels := by
      have ha : raw21576step2 = -raw21576step1 := by apply Matrix.ext; change ∀ i j, raw21576step2 i j = -(raw21576step1 i j); unfold raw21576step2 raw21576step1; decide +kernel
      have hl : raw21576step2Labels = raw21576step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node731 node731Labels := by rfl

def raw21577 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw21577Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21577step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw21577step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21577step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-3, 0, 3]]
def raw21577step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21577step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21577step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21577 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21577 raw21577Labels = mixedMoment B node731 node731Labels := by
  calc
    mixedMoment B raw21577 raw21577Labels = mixedMoment B raw21577step0 raw21577step0Labels := by
      have hz : ∀ j, raw21577 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21577step0 = (fun i j => raw21577 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21577step0 raw21577; decide +kernel
      have hl : raw21577step0Labels = raw21577Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21577 raw21577Labels permutation346 hz
    mixedMoment B raw21577step0 raw21577step0Labels = mixedMoment B raw21577step1 raw21577step1Labels := by
      have ha : raw21577step1 = (fun i j => raw21577step0 (permutation44 i) (permutation4 j)) := by apply Matrix.ext; unfold raw21577step1 raw21577step0; decide +kernel
      have hl : raw21577step1Labels = raw21577step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21577step0 raw21577step0Labels permutation44 permutation4
    mixedMoment B raw21577step1 raw21577step1Labels = mixedMoment B raw21577step2 raw21577step2Labels := by
      have ha : raw21577step2 = -raw21577step1 := by apply Matrix.ext; change ∀ i j, raw21577step2 i j = -(raw21577step1 i j); unfold raw21577step2 raw21577step1; decide +kernel
      have hl : raw21577step2Labels = raw21577step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node731 node731Labels := by rfl

def raw21578 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw21578Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21578step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw21578step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21578step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw21578step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21578step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, 1, 0], ![-3, 0, 3]]
def raw21578step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21578step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw21578step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21578 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21578 raw21578Labels = mixedMoment B node809 node809Labels := by
  calc
    mixedMoment B raw21578 raw21578Labels = mixedMoment B raw21578step0 raw21578step0Labels := by
      have hz : ∀ j, raw21578 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21578step0 = (fun i j => raw21578 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21578step0 raw21578; decide +kernel
      have hl : raw21578step0Labels = raw21578Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21578 raw21578Labels permutation434 hz
    mixedMoment B raw21578step0 raw21578step0Labels = mixedMoment B raw21578step1 raw21578step1Labels := by
      have hz : ∀ j, raw21578step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21578step1 = (fun i j => raw21578step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21578step1 raw21578step0; decide +kernel
      have hl : raw21578step1Labels = raw21578step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21578step0 raw21578step0Labels permutation80 hz
    mixedMoment B raw21578step1 raw21578step1Labels = mixedMoment B raw21578step2 raw21578step2Labels := by
      have ha : raw21578step2 = (fun i j => raw21578step1 (permutation10 i) (permutation4 j)) := by apply Matrix.ext; unfold raw21578step2 raw21578step1; decide +kernel
      have hl : raw21578step2Labels = raw21578step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21578step1 raw21578step1Labels permutation10 permutation4
    mixedMoment B raw21578step2 raw21578step2Labels = mixedMoment B raw21578step3 raw21578step3Labels := by
      have ha : raw21578step3 = -raw21578step2 := by apply Matrix.ext; change ∀ i j, raw21578step3 i j = -(raw21578step2 i j); unfold raw21578step3 raw21578step2; decide +kernel
      have hl : raw21578step3Labels = raw21578step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node809 node809Labels := by rfl

def raw21579 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![1, -4, 3]]
def raw21579Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21579step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![1, -4, 3]]
def raw21579step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21579step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![-2, 1, 1], ![1, -4, 3]]
def raw21579step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21579step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![1, -2, 1], ![-1, 1, 0], ![-4, 1, 3]]
def raw21579step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21579step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![4, -1, -3]]
def raw21579step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21579 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21579 raw21579Labels = mixedMoment B node735 node735Labels := by
  calc
    mixedMoment B raw21579 raw21579Labels = mixedMoment B raw21579step0 raw21579step0Labels := by
      have hz : ∀ j, raw21579 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21579step0 = (fun i j => raw21579 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21579step0 raw21579; decide +kernel
      have hl : raw21579step0Labels = raw21579Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21579 raw21579Labels permutation434 hz
    mixedMoment B raw21579step0 raw21579step0Labels = mixedMoment B raw21579step1 raw21579step1Labels := by
      have hz : ∀ j, raw21579step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21579step1 = (fun i j => raw21579step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21579step1 raw21579step0; decide +kernel
      have hl : raw21579step1Labels = raw21579step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21579step0 raw21579step0Labels permutation80 hz
    mixedMoment B raw21579step1 raw21579step1Labels = mixedMoment B raw21579step2 raw21579step2Labels := by
      have ha : raw21579step2 = (fun i j => raw21579step1 (permutation10 i) (permutation4 j)) := by apply Matrix.ext; unfold raw21579step2 raw21579step1; decide +kernel
      have hl : raw21579step2Labels = raw21579step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21579step1 raw21579step1Labels permutation10 permutation4
    mixedMoment B raw21579step2 raw21579step2Labels = mixedMoment B raw21579step3 raw21579step3Labels := by
      have ha : raw21579step3 = -raw21579step2 := by apply Matrix.ext; change ∀ i j, raw21579step3 i j = -(raw21579step2 i j); unfold raw21579step3 raw21579step2; decide +kernel
      have hl : raw21579step3Labels = raw21579step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node735 node735Labels := by rfl

def raw21580 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw21580Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21580step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw21580step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21580step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw21580step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21580 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21580 raw21580Labels = mixedMoment B node983 node983Labels := by
  calc
    mixedMoment B raw21580 raw21580Labels = mixedMoment B raw21580step0 raw21580step0Labels := by
      have hz : ∀ j, raw21580 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21580step0 = (fun i j => raw21580 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21580step0 raw21580; decide +kernel
      have hl : raw21580step0Labels = raw21580Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21580 raw21580Labels permutation346 hz
    mixedMoment B raw21580step0 raw21580step0Labels = mixedMoment B raw21580step1 raw21580step1Labels := by
      have ha : raw21580step1 = (fun i j => raw21580step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21580step1 raw21580step0; decide +kernel
      have hl : raw21580step1Labels = raw21580step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21580step0 raw21580step0Labels permutation38 permutation2
    _ = mixedMoment B node983 node983Labels := by rfl

def raw21581 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw21581Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21581step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw21581step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21581 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21581 raw21581Labels = mixedMoment B node2080 node2080Labels := by
  calc
    mixedMoment B raw21581 raw21581Labels = mixedMoment B raw21581step0 raw21581step0Labels := by
      have hz : ∀ j, raw21581 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21581step0 = (fun i j => raw21581 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21581step0 raw21581; decide +kernel
      have hl : raw21581step0Labels = raw21581Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21581 raw21581Labels permutation346 hz
    _ = mixedMoment B node2080 node2080Labels := by rfl

def raw21582 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw21582Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21582step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw21582step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21582 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21582 raw21582Labels = mixedMoment B node1988 node1988Labels := by
  calc
    mixedMoment B raw21582 raw21582Labels = mixedMoment B raw21582step0 raw21582step0Labels := by
      have ha : raw21582step0 = (fun i j => raw21582 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21582step0 raw21582; decide +kernel
      have hl : raw21582step0Labels = raw21582Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21582 raw21582Labels permutation182 permutation2
    _ = mixedMoment B node1988 node1988Labels := by rfl

def raw21583 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw21583Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21583step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw21583step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21583step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw21583step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21583 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21583 raw21583Labels = mixedMoment B node1915 node1915Labels := by
  calc
    mixedMoment B raw21583 raw21583Labels = mixedMoment B raw21583step0 raw21583step0Labels := by
      have hz : ∀ j, raw21583 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21583step0 = (fun i j => raw21583 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21583step0 raw21583; decide +kernel
      have hl : raw21583step0Labels = raw21583Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21583 raw21583Labels permutation346 hz
    mixedMoment B raw21583step0 raw21583step0Labels = mixedMoment B raw21583step1 raw21583step1Labels := by
      have ha : raw21583step1 = (fun i j => raw21583step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21583step1 raw21583step0; decide +kernel
      have hl : raw21583step1Labels = raw21583step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21583step0 raw21583step0Labels permutation38 permutation2
    _ = mixedMoment B node1915 node1915Labels := by rfl

def raw21584 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw21584Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21584step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw21584step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21584step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw21584step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21584 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21584 raw21584Labels = mixedMoment B node2197 node2197Labels := by
  calc
    mixedMoment B raw21584 raw21584Labels = mixedMoment B raw21584step0 raw21584step0Labels := by
      have hz : ∀ j, raw21584 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21584step0 = (fun i j => raw21584 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21584step0 raw21584; decide +kernel
      have hl : raw21584step0Labels = raw21584Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21584 raw21584Labels permutation346 hz
    mixedMoment B raw21584step0 raw21584step0Labels = mixedMoment B raw21584step1 raw21584step1Labels := by
      have ha : raw21584step1 = (fun i j => raw21584step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21584step1 raw21584step0; decide +kernel
      have hl : raw21584step1Labels = raw21584step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21584step0 raw21584step0Labels permutation38 permutation2
    _ = mixedMoment B node2197 node2197Labels := by rfl

def raw21585 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw21585Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21585step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw21585step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21585step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw21585step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21585 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21585 raw21585Labels = mixedMoment B node2206 node2206Labels := by
  calc
    mixedMoment B raw21585 raw21585Labels = mixedMoment B raw21585step0 raw21585step0Labels := by
      have hz : ∀ j, raw21585 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21585step0 = (fun i j => raw21585 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21585step0 raw21585; decide +kernel
      have hl : raw21585step0Labels = raw21585Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21585 raw21585Labels permutation346 hz
    mixedMoment B raw21585step0 raw21585step0Labels = mixedMoment B raw21585step1 raw21585step1Labels := by
      have ha : raw21585step1 = (fun i j => raw21585step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21585step1 raw21585step0; decide +kernel
      have hl : raw21585step1Labels = raw21585step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21585step0 raw21585step0Labels permutation38 permutation2
    _ = mixedMoment B node2206 node2206Labels := by rfl

def raw21586 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![0, 0], ![-1, 1], ![2, -2], ![1, -1]]
def raw21586Labels : Fin 2 → Fin 2 := ![0, 1]

def raw21586step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![-1, 1], ![2, -2], ![1, -1]]
def raw21586step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw21586step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw21586step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical21586 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21586 raw21586Labels = mixedMoment B node4080 node4080Labels := by
  calc
    mixedMoment B raw21586 raw21586Labels = mixedMoment B raw21586step0 raw21586step0Labels := by
      have hz : ∀ j, raw21586 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21586step0 = (fun i j => raw21586 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21586step0 raw21586; decide +kernel
      have hl : raw21586step0Labels = raw21586Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21586 raw21586Labels permutation346 hz
    mixedMoment B raw21586step0 raw21586step0Labels = mixedMoment B raw21586step1 raw21586step1Labels := by
      have ha : raw21586step1 = (fun i j => raw21586step0 (permutation39 i) (permutation0 j)) := by apply Matrix.ext; unfold raw21586step1 raw21586step0; decide +kernel
      have hl : raw21586step1Labels = raw21586step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21586step0 raw21586step0Labels permutation39 permutation0
    _ = mixedMoment B node4080 node4080Labels := by rfl

def raw21587 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw21587Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21587step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw21587step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21587step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw21587step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21587 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21587 raw21587Labels = mixedMoment B node1005 node1005Labels := by
  calc
    mixedMoment B raw21587 raw21587Labels = mixedMoment B raw21587step0 raw21587step0Labels := by
      have hz : ∀ j, raw21587 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21587step0 = (fun i j => raw21587 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21587step0 raw21587; decide +kernel
      have hl : raw21587step0Labels = raw21587Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21587 raw21587Labels permutation346 hz
    mixedMoment B raw21587step0 raw21587step0Labels = mixedMoment B raw21587step1 raw21587step1Labels := by
      have ha : raw21587step1 = (fun i j => raw21587step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21587step1 raw21587step0; decide +kernel
      have hl : raw21587step1Labels = raw21587step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21587step0 raw21587step0Labels permutation38 permutation2
    _ = mixedMoment B node1005 node1005Labels := by rfl

def raw21588 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw21588Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21588step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw21588step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21588 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21588 raw21588Labels = mixedMoment B node978 node978Labels := by
  calc
    mixedMoment B raw21588 raw21588Labels = mixedMoment B raw21588step0 raw21588step0Labels := by
      have ha : raw21588step0 = (fun i j => raw21588 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21588step0 raw21588; decide +kernel
      have hl : raw21588step0Labels = raw21588Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21588 raw21588Labels permutation200 permutation2
    _ = mixedMoment B node978 node978Labels := by rfl

def raw21589 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw21589Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21589step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw21589step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21589 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21589 raw21589Labels = mixedMoment B node1036 node1036Labels := by
  calc
    mixedMoment B raw21589 raw21589Labels = mixedMoment B raw21589step0 raw21589step0Labels := by
      have hz : ∀ j, raw21589 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21589step0 = (fun i j => raw21589 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21589step0 raw21589; decide +kernel
      have hl : raw21589step0Labels = raw21589Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21589 raw21589Labels permutation346 hz
    _ = mixedMoment B node1036 node1036Labels := by rfl

def raw21590 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw21590Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21590step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw21590step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21590step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw21590step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21590 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21590 raw21590Labels = mixedMoment B node985 node985Labels := by
  calc
    mixedMoment B raw21590 raw21590Labels = mixedMoment B raw21590step0 raw21590step0Labels := by
      have hz : ∀ j, raw21590 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21590step0 = (fun i j => raw21590 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21590step0 raw21590; decide +kernel
      have hl : raw21590step0Labels = raw21590Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21590 raw21590Labels permutation346 hz
    mixedMoment B raw21590step0 raw21590step0Labels = mixedMoment B raw21590step1 raw21590step1Labels := by
      have ha : raw21590step1 = (fun i j => raw21590step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21590step1 raw21590step0; decide +kernel
      have hl : raw21590step1Labels = raw21590step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21590step0 raw21590step0Labels permutation39 permutation2
    _ = mixedMoment B node985 node985Labels := by rfl

def raw21591 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw21591Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21591step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw21591step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21591step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw21591step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21591 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21591 raw21591Labels = mixedMoment B node982 node982Labels := by
  calc
    mixedMoment B raw21591 raw21591Labels = mixedMoment B raw21591step0 raw21591step0Labels := by
      have hz : ∀ j, raw21591 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21591step0 = (fun i j => raw21591 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21591step0 raw21591; decide +kernel
      have hl : raw21591step0Labels = raw21591Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21591 raw21591Labels permutation346 hz
    mixedMoment B raw21591step0 raw21591step0Labels = mixedMoment B raw21591step1 raw21591step1Labels := by
      have ha : raw21591step1 = (fun i j => raw21591step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21591step1 raw21591step0; decide +kernel
      have hl : raw21591step1Labels = raw21591step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21591step0 raw21591step0Labels permutation38 permutation2
    _ = mixedMoment B node982 node982Labels := by rfl

def raw21592 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw21592Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21592step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw21592step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21592 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21592 raw21592Labels = mixedMoment B node2079 node2079Labels := by
  calc
    mixedMoment B raw21592 raw21592Labels = mixedMoment B raw21592step0 raw21592step0Labels := by
      have hz : ∀ j, raw21592 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21592step0 = (fun i j => raw21592 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21592step0 raw21592; decide +kernel
      have hl : raw21592step0Labels = raw21592Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21592 raw21592Labels permutation346 hz
    _ = mixedMoment B node2079 node2079Labels := by rfl

def raw21593 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw21593Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21593step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw21593step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21593 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21593 raw21593Labels = mixedMoment B node1987 node1987Labels := by
  calc
    mixedMoment B raw21593 raw21593Labels = mixedMoment B raw21593step0 raw21593step0Labels := by
      have ha : raw21593step0 = (fun i j => raw21593 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21593step0 raw21593; decide +kernel
      have hl : raw21593step0Labels = raw21593Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21593 raw21593Labels permutation182 permutation2
    _ = mixedMoment B node1987 node1987Labels := by rfl

def raw21594 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw21594Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21594step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw21594step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21594step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw21594step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21594 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21594 raw21594Labels = mixedMoment B node1914 node1914Labels := by
  calc
    mixedMoment B raw21594 raw21594Labels = mixedMoment B raw21594step0 raw21594step0Labels := by
      have hz : ∀ j, raw21594 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21594step0 = (fun i j => raw21594 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21594step0 raw21594; decide +kernel
      have hl : raw21594step0Labels = raw21594Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21594 raw21594Labels permutation346 hz
    mixedMoment B raw21594step0 raw21594step0Labels = mixedMoment B raw21594step1 raw21594step1Labels := by
      have ha : raw21594step1 = (fun i j => raw21594step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21594step1 raw21594step0; decide +kernel
      have hl : raw21594step1Labels = raw21594step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21594step0 raw21594step0Labels permutation38 permutation2
    _ = mixedMoment B node1914 node1914Labels := by rfl

def raw21595 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw21595Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21595step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw21595step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21595step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw21595step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21595 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21595 raw21595Labels = mixedMoment B node2193 node2193Labels := by
  calc
    mixedMoment B raw21595 raw21595Labels = mixedMoment B raw21595step0 raw21595step0Labels := by
      have hz : ∀ j, raw21595 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21595step0 = (fun i j => raw21595 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21595step0 raw21595; decide +kernel
      have hl : raw21595step0Labels = raw21595Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21595 raw21595Labels permutation346 hz
    mixedMoment B raw21595step0 raw21595step0Labels = mixedMoment B raw21595step1 raw21595step1Labels := by
      have ha : raw21595step1 = (fun i j => raw21595step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21595step1 raw21595step0; decide +kernel
      have hl : raw21595step1Labels = raw21595step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21595step0 raw21595step0Labels permutation38 permutation2
    _ = mixedMoment B node2193 node2193Labels := by rfl

def raw21596 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw21596Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21596step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw21596step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21596step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw21596step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21596 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21596 raw21596Labels = mixedMoment B node2205 node2205Labels := by
  calc
    mixedMoment B raw21596 raw21596Labels = mixedMoment B raw21596step0 raw21596step0Labels := by
      have hz : ∀ j, raw21596 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21596step0 = (fun i j => raw21596 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21596step0 raw21596; decide +kernel
      have hl : raw21596step0Labels = raw21596Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21596 raw21596Labels permutation346 hz
    mixedMoment B raw21596step0 raw21596step0Labels = mixedMoment B raw21596step1 raw21596step1Labels := by
      have ha : raw21596step1 = (fun i j => raw21596step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21596step1 raw21596step0; decide +kernel
      have hl : raw21596step1Labels = raw21596step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21596step0 raw21596step0Labels permutation38 permutation2
    _ = mixedMoment B node2205 node2205Labels := by rfl

def raw21597 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![0, 0], ![-1, 1], ![1, -1], ![2, -2]]
def raw21597Labels : Fin 2 → Fin 2 := ![0, 1]

def raw21597step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![-1, 1], ![1, -1], ![2, -2]]
def raw21597step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw21597step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw21597step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical21597 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21597 raw21597Labels = mixedMoment B node4080 node4080Labels := by
  calc
    mixedMoment B raw21597 raw21597Labels = mixedMoment B raw21597step0 raw21597step0Labels := by
      have hz : ∀ j, raw21597 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21597step0 = (fun i j => raw21597 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21597step0 raw21597; decide +kernel
      have hl : raw21597step0Labels = raw21597Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21597 raw21597Labels permutation346 hz
    mixedMoment B raw21597step0 raw21597step0Labels = mixedMoment B raw21597step1 raw21597step1Labels := by
      have ha : raw21597step1 = (fun i j => raw21597step0 (permutation38 i) (permutation0 j)) := by apply Matrix.ext; unfold raw21597step1 raw21597step0; decide +kernel
      have hl : raw21597step1Labels = raw21597step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21597step0 raw21597step0Labels permutation38 permutation0
    _ = mixedMoment B node4080 node4080Labels := by rfl

def raw21598 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw21598Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21598step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw21598step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21598step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw21598step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21598 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21598 raw21598Labels = mixedMoment B node572 node572Labels := by
  calc
    mixedMoment B raw21598 raw21598Labels = mixedMoment B raw21598step0 raw21598step0Labels := by
      have hz : ∀ j, raw21598 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21598step0 = (fun i j => raw21598 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21598step0 raw21598; decide +kernel
      have hl : raw21598step0Labels = raw21598Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21598 raw21598Labels permutation346 hz
    mixedMoment B raw21598step0 raw21598step0Labels = mixedMoment B raw21598step1 raw21598step1Labels := by
      have ha : raw21598step1 = (fun i j => raw21598step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21598step1 raw21598step0; decide +kernel
      have hl : raw21598step1Labels = raw21598step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21598step0 raw21598step0Labels permutation38 permutation2
    _ = mixedMoment B node572 node572Labels := by rfl

def raw21599 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw21599Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21599step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw21599step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21599 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21599 raw21599Labels = mixedMoment B node900 node900Labels := by
  calc
    mixedMoment B raw21599 raw21599Labels = mixedMoment B raw21599step0 raw21599step0Labels := by
      have ha : raw21599step0 = (fun i j => raw21599 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21599step0 raw21599; decide +kernel
      have hl : raw21599step0Labels = raw21599Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21599 raw21599Labels permutation182 permutation2
    _ = mixedMoment B node900 node900Labels := by rfl

def raw21600 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw21600Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21600step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw21600step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21600step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw21600step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21600 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21600 raw21600Labels = mixedMoment B node886 node886Labels := by
  calc
    mixedMoment B raw21600 raw21600Labels = mixedMoment B raw21600step0 raw21600step0Labels := by
      have hz : ∀ j, raw21600 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21600step0 = (fun i j => raw21600 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21600step0 raw21600; decide +kernel
      have hl : raw21600step0Labels = raw21600Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21600 raw21600Labels permutation346 hz
    mixedMoment B raw21600step0 raw21600step0Labels = mixedMoment B raw21600step1 raw21600step1Labels := by
      have ha : raw21600step1 = (fun i j => raw21600step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21600step1 raw21600step0; decide +kernel
      have hl : raw21600step1Labels = raw21600step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21600step0 raw21600step0Labels permutation38 permutation2
    _ = mixedMoment B node886 node886Labels := by rfl

def raw21601 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw21601Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21601step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw21601step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21601step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw21601step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21601 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21601 raw21601Labels = mixedMoment B node982 node982Labels := by
  calc
    mixedMoment B raw21601 raw21601Labels = mixedMoment B raw21601step0 raw21601step0Labels := by
      have hz : ∀ j, raw21601 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21601step0 = (fun i j => raw21601 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21601step0 raw21601; decide +kernel
      have hl : raw21601step0Labels = raw21601Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21601 raw21601Labels permutation346 hz
    mixedMoment B raw21601step0 raw21601step0Labels = mixedMoment B raw21601step1 raw21601step1Labels := by
      have ha : raw21601step1 = (fun i j => raw21601step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21601step1 raw21601step0; decide +kernel
      have hl : raw21601step1Labels = raw21601step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21601step0 raw21601step0Labels permutation40 permutation2
    _ = mixedMoment B node982 node982Labels := by rfl

def raw21602 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw21602Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21602step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw21602step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21602step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw21602step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21602 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21602 raw21602Labels = mixedMoment B node1004 node1004Labels := by
  calc
    mixedMoment B raw21602 raw21602Labels = mixedMoment B raw21602step0 raw21602step0Labels := by
      have hz : ∀ j, raw21602 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21602step0 = (fun i j => raw21602 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21602step0 raw21602; decide +kernel
      have hl : raw21602step0Labels = raw21602Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21602 raw21602Labels permutation346 hz
    mixedMoment B raw21602step0 raw21602step0Labels = mixedMoment B raw21602step1 raw21602step1Labels := by
      have ha : raw21602step1 = (fun i j => raw21602step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21602step1 raw21602step0; decide +kernel
      have hl : raw21602step1Labels = raw21602step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21602step0 raw21602step0Labels permutation38 permutation2
    _ = mixedMoment B node1004 node1004Labels := by rfl

def raw21603 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw21603Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21603step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21603step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21603 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21603 raw21603Labels = mixedMoment B node865 node865Labels := by
  calc
    mixedMoment B raw21603 raw21603Labels = mixedMoment B raw21603step0 raw21603step0Labels := by
      have ha : raw21603step0 = (fun i j => raw21603 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21603step0 raw21603; decide +kernel
      have hl : raw21603step0Labels = raw21603Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21603 raw21603Labels permutation200 permutation2
    _ = mixedMoment B node865 node865Labels := by rfl

def raw21604 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![2, -1, -1], ![3, -1, -2]]
def raw21604Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21604step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 0, 1], ![2, -1, -1], ![3, -1, -2]]
def raw21604step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21604step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw21604step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21604 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21604 raw21604Labels = mixedMoment B node873 node873Labels := by
  calc
    mixedMoment B raw21604 raw21604Labels = mixedMoment B raw21604step0 raw21604step0Labels := by
      have hz : ∀ j, raw21604 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21604step0 = (fun i j => raw21604 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21604step0 raw21604; decide +kernel
      have hl : raw21604step0Labels = raw21604Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21604 raw21604Labels permutation346 hz
    mixedMoment B raw21604step0 raw21604step0Labels = mixedMoment B raw21604step1 raw21604step1Labels := by
      have ha : raw21604step1 = (fun i j => raw21604step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21604step1 raw21604step0; decide +kernel
      have hl : raw21604step1Labels = raw21604step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21604step0 raw21604step0Labels permutation38 permutation2
    _ = mixedMoment B node873 node873Labels := by rfl

def raw21605 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw21605Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21605step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw21605step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21605step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![4, -2, -2]]
def raw21605step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21605 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21605 raw21605Labels = mixedMoment B node871 node871Labels := by
  calc
    mixedMoment B raw21605 raw21605Labels = mixedMoment B raw21605step0 raw21605step0Labels := by
      have hz : ∀ j, raw21605 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21605step0 = (fun i j => raw21605 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21605step0 raw21605; decide +kernel
      have hl : raw21605step0Labels = raw21605Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21605 raw21605Labels permutation346 hz
    mixedMoment B raw21605step0 raw21605step0Labels = mixedMoment B raw21605step1 raw21605step1Labels := by
      have ha : raw21605step1 = (fun i j => raw21605step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21605step1 raw21605step0; decide +kernel
      have hl : raw21605step1Labels = raw21605step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21605step0 raw21605step0Labels permutation38 permutation2
    _ = mixedMoment B node871 node871Labels := by rfl

def raw21606 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw21606Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21606step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw21606step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21606 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21606 raw21606Labels = mixedMoment B node977 node977Labels := by
  calc
    mixedMoment B raw21606 raw21606Labels = mixedMoment B raw21606step0 raw21606step0Labels := by
      have ha : raw21606step0 = (fun i j => raw21606 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21606step0 raw21606; decide +kernel
      have hl : raw21606step0Labels = raw21606Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21606 raw21606Labels permutation200 permutation2
    _ = mixedMoment B node977 node977Labels := by rfl

def raw21607 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw21607Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21607step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw21607step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21607 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21607 raw21607Labels = mixedMoment B node1035 node1035Labels := by
  calc
    mixedMoment B raw21607 raw21607Labels = mixedMoment B raw21607step0 raw21607step0Labels := by
      have hz : ∀ j, raw21607 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21607step0 = (fun i j => raw21607 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21607step0 raw21607; decide +kernel
      have hl : raw21607step0Labels = raw21607Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21607 raw21607Labels permutation346 hz
    _ = mixedMoment B node1035 node1035Labels := by rfl

def raw21608 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw21608Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21608step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw21608step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21608step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw21608step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21608 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21608 raw21608Labels = mixedMoment B node985 node985Labels := by
  calc
    mixedMoment B raw21608 raw21608Labels = mixedMoment B raw21608step0 raw21608step0Labels := by
      have hz : ∀ j, raw21608 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21608step0 = (fun i j => raw21608 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21608step0 raw21608; decide +kernel
      have hl : raw21608step0Labels = raw21608Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21608 raw21608Labels permutation346 hz
    mixedMoment B raw21608step0 raw21608step0Labels = mixedMoment B raw21608step1 raw21608step1Labels := by
      have ha : raw21608step1 = (fun i j => raw21608step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21608step1 raw21608step0; decide +kernel
      have hl : raw21608step1Labels = raw21608step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21608step0 raw21608step0Labels permutation38 permutation2
    _ = mixedMoment B node985 node985Labels := by rfl

def raw21609 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw21609Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21609step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw21609step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21609step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![-1, 0, 1], ![-2, 2, 0], ![-2, -1, 3]]
def raw21609step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21609step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def raw21609step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21609 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21609 raw21609Labels = mixedMoment B node721 node721Labels := by
  calc
    mixedMoment B raw21609 raw21609Labels = mixedMoment B raw21609step0 raw21609step0Labels := by
      have hz : ∀ j, raw21609 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21609step0 = (fun i j => raw21609 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21609step0 raw21609; decide +kernel
      have hl : raw21609step0Labels = raw21609Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21609 raw21609Labels permutation346 hz
    mixedMoment B raw21609step0 raw21609step0Labels = mixedMoment B raw21609step1 raw21609step1Labels := by
      have ha : raw21609step1 = (fun i j => raw21609step0 (permutation40 i) (permutation4 j)) := by apply Matrix.ext; unfold raw21609step1 raw21609step0; decide +kernel
      have hl : raw21609step1Labels = raw21609step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21609step0 raw21609step0Labels permutation40 permutation4
    mixedMoment B raw21609step1 raw21609step1Labels = mixedMoment B raw21609step2 raw21609step2Labels := by
      have ha : raw21609step2 = -raw21609step1 := by apply Matrix.ext; change ∀ i j, raw21609step2 i j = -(raw21609step1 i j); unfold raw21609step2 raw21609step1; decide +kernel
      have hl : raw21609step2Labels = raw21609step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node721 node721Labels := by rfl

def raw21610 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw21610Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21610step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw21610step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21610step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw21610step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21610 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21610 raw21610Labels = mixedMoment B node709 node709Labels := by
  calc
    mixedMoment B raw21610 raw21610Labels = mixedMoment B raw21610step0 raw21610step0Labels := by
      have ha : raw21610step0 = (fun i j => raw21610 (permutation200 i) (permutation4 j)) := by apply Matrix.ext; unfold raw21610step0 raw21610; decide +kernel
      have hl : raw21610step0Labels = raw21610Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21610 raw21610Labels permutation200 permutation4
    mixedMoment B raw21610step0 raw21610step0Labels = mixedMoment B raw21610step1 raw21610step1Labels := by
      have ha : raw21610step1 = -raw21610step0 := by apply Matrix.ext; change ∀ i j, raw21610step1 i j = -(raw21610step0 i j); unfold raw21610step1 raw21610step0; decide +kernel
      have hl : raw21610step1Labels = raw21610step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node709 node709Labels := by rfl

def raw21611 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw21611Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21611step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw21611step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21611step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![-1, 1, 0], ![-2, 1, 1], ![-2, -1, 3]]
def raw21611step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21611step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw21611step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21611 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21611 raw21611Labels = mixedMoment B node716 node716Labels := by
  calc
    mixedMoment B raw21611 raw21611Labels = mixedMoment B raw21611step0 raw21611step0Labels := by
      have hz : ∀ j, raw21611 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21611step0 = (fun i j => raw21611 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21611step0 raw21611; decide +kernel
      have hl : raw21611step0Labels = raw21611Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21611 raw21611Labels permutation346 hz
    mixedMoment B raw21611step0 raw21611step0Labels = mixedMoment B raw21611step1 raw21611step1Labels := by
      have ha : raw21611step1 = (fun i j => raw21611step0 (permutation38 i) (permutation4 j)) := by apply Matrix.ext; unfold raw21611step1 raw21611step0; decide +kernel
      have hl : raw21611step1Labels = raw21611step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21611step0 raw21611step0Labels permutation38 permutation4
    mixedMoment B raw21611step1 raw21611step1Labels = mixedMoment B raw21611step2 raw21611step2Labels := by
      have ha : raw21611step2 = -raw21611step1 := by apply Matrix.ext; change ∀ i j, raw21611step2 i j = -(raw21611step1 i j); unfold raw21611step2 raw21611step1; decide +kernel
      have hl : raw21611step2Labels = raw21611step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node716 node716Labels := by rfl

def raw21612 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -3, 3]]
def raw21612Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21612step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -3, 3]]
def raw21612step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21612step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-3, 0, 3]]
def raw21612step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21612step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw21612step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21612 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21612 raw21612Labels = mixedMoment B node714 node714Labels := by
  calc
    mixedMoment B raw21612 raw21612Labels = mixedMoment B raw21612step0 raw21612step0Labels := by
      have hz : ∀ j, raw21612 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21612step0 = (fun i j => raw21612 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21612step0 raw21612; decide +kernel
      have hl : raw21612step0Labels = raw21612Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21612 raw21612Labels permutation346 hz
    mixedMoment B raw21612step0 raw21612step0Labels = mixedMoment B raw21612step1 raw21612step1Labels := by
      have ha : raw21612step1 = (fun i j => raw21612step0 (permutation38 i) (permutation4 j)) := by apply Matrix.ext; unfold raw21612step1 raw21612step0; decide +kernel
      have hl : raw21612step1Labels = raw21612step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21612step0 raw21612step0Labels permutation38 permutation4
    mixedMoment B raw21612step1 raw21612step1Labels = mixedMoment B raw21612step2 raw21612step2Labels := by
      have ha : raw21612step2 = -raw21612step1 := by apply Matrix.ext; change ∀ i j, raw21612step2 i j = -(raw21612step1 i j); unfold raw21612step2 raw21612step1; decide +kernel
      have hl : raw21612step2Labels = raw21612step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node714 node714Labels := by rfl

def raw21613 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw21613Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21613step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw21613step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21613step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw21613step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21613 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21613 raw21613Labels = mixedMoment B node979 node979Labels := by
  calc
    mixedMoment B raw21613 raw21613Labels = mixedMoment B raw21613step0 raw21613step0Labels := by
      have hz : ∀ j, raw21613 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21613step0 = (fun i j => raw21613 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21613step0 raw21613; decide +kernel
      have hl : raw21613step0Labels = raw21613Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21613 raw21613Labels permutation346 hz
    mixedMoment B raw21613step0 raw21613step0Labels = mixedMoment B raw21613step1 raw21613step1Labels := by
      have ha : raw21613step1 = (fun i j => raw21613step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21613step1 raw21613step0; decide +kernel
      have hl : raw21613step1Labels = raw21613step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21613step0 raw21613step0Labels permutation38 permutation2
    _ = mixedMoment B node979 node979Labels := by rfl

def raw21614 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw21614Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21614step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw21614step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21614step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-3, 0, 3]]
def raw21614step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21614step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw21614step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21614 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21614 raw21614Labels = mixedMoment B node2018 node2018Labels := by
  calc
    mixedMoment B raw21614 raw21614Labels = mixedMoment B raw21614step0 raw21614step0Labels := by
      have hz : ∀ j, raw21614 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21614step0 = (fun i j => raw21614 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21614step0 raw21614; decide +kernel
      have hl : raw21614step0Labels = raw21614Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21614 raw21614Labels permutation346 hz
    mixedMoment B raw21614step0 raw21614step0Labels = mixedMoment B raw21614step1 raw21614step1Labels := by
      have ha : raw21614step1 = (fun i j => raw21614step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21614step1 raw21614step0; decide +kernel
      have hl : raw21614step1Labels = raw21614step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21614step0 raw21614step0Labels permutation151 permutation2
    mixedMoment B raw21614step1 raw21614step1Labels = mixedMoment B raw21614step2 raw21614step2Labels := by
      have ha : raw21614step2 = -raw21614step1 := by apply Matrix.ext; change ∀ i j, raw21614step2 i j = -(raw21614step1 i j); unfold raw21614step2 raw21614step1; decide +kernel
      have hl : raw21614step2Labels = raw21614step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2018 node2018Labels := by rfl

def raw21615 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw21615Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21615step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw21615step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21615 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21615 raw21615Labels = mixedMoment B node1986 node1986Labels := by
  calc
    mixedMoment B raw21615 raw21615Labels = mixedMoment B raw21615step0 raw21615step0Labels := by
      have ha : raw21615step0 = (fun i j => raw21615 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21615step0 raw21615; decide +kernel
      have hl : raw21615step0Labels = raw21615Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21615 raw21615Labels permutation182 permutation2
    _ = mixedMoment B node1986 node1986Labels := by rfl

def raw21616 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw21616Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21616step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw21616step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21616step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw21616step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21616 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21616 raw21616Labels = mixedMoment B node1911 node1911Labels := by
  calc
    mixedMoment B raw21616 raw21616Labels = mixedMoment B raw21616step0 raw21616step0Labels := by
      have hz : ∀ j, raw21616 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21616step0 = (fun i j => raw21616 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21616step0 raw21616; decide +kernel
      have hl : raw21616step0Labels = raw21616Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21616 raw21616Labels permutation346 hz
    mixedMoment B raw21616step0 raw21616step0Labels = mixedMoment B raw21616step1 raw21616step1Labels := by
      have ha : raw21616step1 = (fun i j => raw21616step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21616step1 raw21616step0; decide +kernel
      have hl : raw21616step1Labels = raw21616step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21616step0 raw21616step0Labels permutation38 permutation2
    _ = mixedMoment B node1911 node1911Labels := by rfl

def raw21617 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![3, 0, -3]]
def raw21617Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21617step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw21617step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21617step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, -1, 1], ![3, 0, -3]]
def raw21617step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21617step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![3, 0, -3]]
def raw21617step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21617 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21617 raw21617Labels = mixedMoment B node2208 node2208Labels := by
  calc
    mixedMoment B raw21617 raw21617Labels = mixedMoment B raw21617step0 raw21617step0Labels := by
      have hz : ∀ j, raw21617 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw21617step0 = (fun i j => raw21617 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw21617step0 raw21617; decide +kernel
      have hl : raw21617step0Labels = raw21617Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21617 raw21617Labels permutation520 hz
    mixedMoment B raw21617step0 raw21617step0Labels = mixedMoment B raw21617step1 raw21617step1Labels := by
      have hz : ∀ j, raw21617step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21617step1 = (fun i j => raw21617step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21617step1 raw21617step0; decide +kernel
      have hl : raw21617step1Labels = raw21617step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21617step0 raw21617step0Labels permutation80 hz
    mixedMoment B raw21617step1 raw21617step1Labels = mixedMoment B raw21617step2 raw21617step2Labels := by
      have ha : raw21617step2 = (fun i j => raw21617step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21617step2 raw21617step1; decide +kernel
      have hl : raw21617step2Labels = raw21617step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21617step1 raw21617step1Labels permutation10 permutation2
    _ = mixedMoment B node2208 node2208Labels := by rfl

def raw21618 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw21618Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21618step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw21618step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21618step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw21618step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21618 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21618 raw21618Labels = mixedMoment B node2203 node2203Labels := by
  calc
    mixedMoment B raw21618 raw21618Labels = mixedMoment B raw21618step0 raw21618step0Labels := by
      have hz : ∀ j, raw21618 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21618step0 = (fun i j => raw21618 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21618step0 raw21618; decide +kernel
      have hl : raw21618step0Labels = raw21618Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21618 raw21618Labels permutation346 hz
    mixedMoment B raw21618step0 raw21618step0Labels = mixedMoment B raw21618step1 raw21618step1Labels := by
      have ha : raw21618step1 = (fun i j => raw21618step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21618step1 raw21618step0; decide +kernel
      have hl : raw21618step1Labels = raw21618step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21618step0 raw21618step0Labels permutation38 permutation2
    _ = mixedMoment B node2203 node2203Labels := by rfl

def raw21619 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![0, 0], ![-1, 1], ![0, 0], ![3, -3]]
def raw21619Labels : Fin 2 → Fin 2 := ![0, 1]

def raw21619step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![0, 0], ![-1, 1], ![3, -3]]
def raw21619step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw21619step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![-1, 1], ![3, -3]]
def raw21619step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw21619step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![3, -3]]
def raw21619step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical21619 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21619 raw21619Labels = mixedMoment B node4081 node4081Labels := by
  calc
    mixedMoment B raw21619 raw21619Labels = mixedMoment B raw21619step0 raw21619step0Labels := by
      have hz : ∀ j, raw21619 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw21619step0 = (fun i j => raw21619 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw21619step0 raw21619; decide +kernel
      have hl : raw21619step0Labels = raw21619Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21619 raw21619Labels permutation520 hz
    mixedMoment B raw21619step0 raw21619step0Labels = mixedMoment B raw21619step1 raw21619step1Labels := by
      have hz : ∀ j, raw21619step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21619step1 = (fun i j => raw21619step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21619step1 raw21619step0; decide +kernel
      have hl : raw21619step1Labels = raw21619step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21619step0 raw21619step0Labels permutation80 hz
    mixedMoment B raw21619step1 raw21619step1Labels = mixedMoment B raw21619step2 raw21619step2Labels := by
      have ha : raw21619step2 = (fun i j => raw21619step1 (permutation10 i) (permutation0 j)) := by apply Matrix.ext; unfold raw21619step2 raw21619step1; decide +kernel
      have hl : raw21619step2Labels = raw21619step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21619step1 raw21619step1Labels permutation10 permutation0
    _ = mixedMoment B node4081 node4081Labels := by rfl

def raw21620 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw21620Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21620step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw21620step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21620step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw21620step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21620 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21620 raw21620Labels = mixedMoment B node568 node568Labels := by
  calc
    mixedMoment B raw21620 raw21620Labels = mixedMoment B raw21620step0 raw21620step0Labels := by
      have hz : ∀ j, raw21620 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21620step0 = (fun i j => raw21620 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21620step0 raw21620; decide +kernel
      have hl : raw21620step0Labels = raw21620Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21620 raw21620Labels permutation346 hz
    mixedMoment B raw21620step0 raw21620step0Labels = mixedMoment B raw21620step1 raw21620step1Labels := by
      have ha : raw21620step1 = (fun i j => raw21620step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21620step1 raw21620step0; decide +kernel
      have hl : raw21620step1Labels = raw21620step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21620step0 raw21620step0Labels permutation40 permutation2
    _ = mixedMoment B node568 node568Labels := by rfl

def raw21621 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw21621Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21621step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw21621step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21621 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21621 raw21621Labels = mixedMoment B node898 node898Labels := by
  calc
    mixedMoment B raw21621 raw21621Labels = mixedMoment B raw21621step0 raw21621step0Labels := by
      have ha : raw21621step0 = (fun i j => raw21621 (permutation184 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21621step0 raw21621; decide +kernel
      have hl : raw21621step0Labels = raw21621Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21621 raw21621Labels permutation184 permutation2
    _ = mixedMoment B node898 node898Labels := by rfl

def raw21622 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw21622Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21622step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw21622step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21622step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw21622step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21622 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21622 raw21622Labels = mixedMoment B node880 node880Labels := by
  calc
    mixedMoment B raw21622 raw21622Labels = mixedMoment B raw21622step0 raw21622step0Labels := by
      have hz : ∀ j, raw21622 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21622step0 = (fun i j => raw21622 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21622step0 raw21622; decide +kernel
      have hl : raw21622step0Labels = raw21622Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21622 raw21622Labels permutation346 hz
    mixedMoment B raw21622step0 raw21622step0Labels = mixedMoment B raw21622step1 raw21622step1Labels := by
      have ha : raw21622step1 = (fun i j => raw21622step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21622step1 raw21622step0; decide +kernel
      have hl : raw21622step1Labels = raw21622step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21622step0 raw21622step0Labels permutation40 permutation2
    _ = mixedMoment B node880 node880Labels := by rfl

def raw21623 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![3, 0, -3]]
def raw21623Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21623step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw21623step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21623step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, -1, 1], ![3, 0, -3]]
def raw21623step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21623step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21623step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21623 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21623 raw21623Labels = mixedMoment B node1007 node1007Labels := by
  calc
    mixedMoment B raw21623 raw21623Labels = mixedMoment B raw21623step0 raw21623step0Labels := by
      have hz : ∀ j, raw21623 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw21623step0 = (fun i j => raw21623 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw21623step0 raw21623; decide +kernel
      have hl : raw21623step0Labels = raw21623Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21623 raw21623Labels permutation520 hz
    mixedMoment B raw21623step0 raw21623step0Labels = mixedMoment B raw21623step1 raw21623step1Labels := by
      have hz : ∀ j, raw21623step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21623step1 = (fun i j => raw21623step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21623step1 raw21623step0; decide +kernel
      have hl : raw21623step1Labels = raw21623step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21623step0 raw21623step0Labels permutation80 hz
    mixedMoment B raw21623step1 raw21623step1Labels = mixedMoment B raw21623step2 raw21623step2Labels := by
      have ha : raw21623step2 = (fun i j => raw21623step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21623step2 raw21623step1; decide +kernel
      have hl : raw21623step2Labels = raw21623step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21623step1 raw21623step1Labels permutation10 permutation2
    _ = mixedMoment B node1007 node1007Labels := by rfl

def raw21624 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw21624Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21624step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw21624step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21624step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw21624step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21624 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21624 raw21624Labels = mixedMoment B node999 node999Labels := by
  calc
    mixedMoment B raw21624 raw21624Labels = mixedMoment B raw21624step0 raw21624step0Labels := by
      have hz : ∀ j, raw21624 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21624step0 = (fun i j => raw21624 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21624step0 raw21624; decide +kernel
      have hl : raw21624step0Labels = raw21624Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21624 raw21624Labels permutation346 hz
    mixedMoment B raw21624step0 raw21624step0Labels = mixedMoment B raw21624step1 raw21624step1Labels := by
      have ha : raw21624step1 = (fun i j => raw21624step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21624step1 raw21624step0; decide +kernel
      have hl : raw21624step1Labels = raw21624step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21624step0 raw21624step0Labels permutation40 permutation2
    _ = mixedMoment B node999 node999Labels := by rfl

def raw21625 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw21625Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21625step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21625step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21625 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21625 raw21625Labels = mixedMoment B node864 node864Labels := by
  calc
    mixedMoment B raw21625 raw21625Labels = mixedMoment B raw21625step0 raw21625step0Labels := by
      have ha : raw21625step0 = (fun i j => raw21625 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21625step0 raw21625; decide +kernel
      have hl : raw21625step0Labels = raw21625Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21625 raw21625Labels permutation200 permutation2
    _ = mixedMoment B node864 node864Labels := by rfl

def raw21626 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def raw21626Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21626step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def raw21626step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21626step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![3, 0, -3]]
def raw21626step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21626 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21626 raw21626Labels = mixedMoment B node872 node872Labels := by
  calc
    mixedMoment B raw21626 raw21626Labels = mixedMoment B raw21626step0 raw21626step0Labels := by
      have hz : ∀ j, raw21626 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21626step0 = (fun i j => raw21626 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21626step0 raw21626; decide +kernel
      have hl : raw21626step0Labels = raw21626Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21626 raw21626Labels permutation346 hz
    mixedMoment B raw21626step0 raw21626step0Labels = mixedMoment B raw21626step1 raw21626step1Labels := by
      have ha : raw21626step1 = (fun i j => raw21626step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21626step1 raw21626step0; decide +kernel
      have hl : raw21626step1Labels = raw21626step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21626step0 raw21626step0Labels permutation38 permutation2
    _ = mixedMoment B node872 node872Labels := by rfl

def raw21627 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![4, -1, -3]]
def raw21627Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21627step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 0, 1], ![1, -1, 0], ![4, -1, -3]]
def raw21627step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21627step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![4, -1, -3]]
def raw21627step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21627 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21627 raw21627Labels = mixedMoment B node867 node867Labels := by
  calc
    mixedMoment B raw21627 raw21627Labels = mixedMoment B raw21627step0 raw21627step0Labels := by
      have hz : ∀ j, raw21627 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21627step0 = (fun i j => raw21627 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21627step0 raw21627; decide +kernel
      have hl : raw21627step0Labels = raw21627Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21627 raw21627Labels permutation346 hz
    mixedMoment B raw21627step0 raw21627step0Labels = mixedMoment B raw21627step1 raw21627step1Labels := by
      have ha : raw21627step1 = (fun i j => raw21627step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21627step1 raw21627step0; decide +kernel
      have hl : raw21627step1Labels = raw21627step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21627step0 raw21627step0Labels permutation38 permutation2
    _ = mixedMoment B node867 node867Labels := by rfl

def raw21628 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw21628Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21628step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw21628step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21628 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21628 raw21628Labels = mixedMoment B node976 node976Labels := by
  calc
    mixedMoment B raw21628 raw21628Labels = mixedMoment B raw21628step0 raw21628step0Labels := by
      have ha : raw21628step0 = (fun i j => raw21628 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21628step0 raw21628; decide +kernel
      have hl : raw21628step0Labels = raw21628Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21628 raw21628Labels permutation200 permutation2
    _ = mixedMoment B node976 node976Labels := by rfl

def raw21629 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw21629Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21629step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw21629step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21629 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21629 raw21629Labels = mixedMoment B node1033 node1033Labels := by
  calc
    mixedMoment B raw21629 raw21629Labels = mixedMoment B raw21629step0 raw21629step0Labels := by
      have hz : ∀ j, raw21629 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21629step0 = (fun i j => raw21629 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21629step0 raw21629; decide +kernel
      have hl : raw21629step0Labels = raw21629Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21629 raw21629Labels permutation346 hz
    _ = mixedMoment B node1033 node1033Labels := by rfl

def raw21630 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw21630Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21630step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw21630step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21630step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw21630step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21630 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21630 raw21630Labels = mixedMoment B node984 node984Labels := by
  calc
    mixedMoment B raw21630 raw21630Labels = mixedMoment B raw21630step0 raw21630step0Labels := by
      have hz : ∀ j, raw21630 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21630step0 = (fun i j => raw21630 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21630step0 raw21630; decide +kernel
      have hl : raw21630step0Labels = raw21630Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21630 raw21630Labels permutation346 hz
    mixedMoment B raw21630step0 raw21630step0Labels = mixedMoment B raw21630step1 raw21630step1Labels := by
      have ha : raw21630step1 = (fun i j => raw21630step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21630step1 raw21630step0; decide +kernel
      have hl : raw21630step1Labels = raw21630step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21630step0 raw21630step0Labels permutation38 permutation2
    _ = mixedMoment B node984 node984Labels := by rfl

def raw21631 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw21631Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21631step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw21631step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21631step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![0, -1, 1], ![-2, 2, 0], ![-3, 0, 3]]
def raw21631step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21631step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![3, 0, -3]]
def raw21631step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21631 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21631 raw21631Labels = mixedMoment B node706 node706Labels := by
  calc
    mixedMoment B raw21631 raw21631Labels = mixedMoment B raw21631step0 raw21631step0Labels := by
      have hz : ∀ j, raw21631 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21631step0 = (fun i j => raw21631 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21631step0 raw21631; decide +kernel
      have hl : raw21631step0Labels = raw21631Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21631 raw21631Labels permutation346 hz
    mixedMoment B raw21631step0 raw21631step0Labels = mixedMoment B raw21631step1 raw21631step1Labels := by
      have ha : raw21631step1 = (fun i j => raw21631step0 (permutation40 i) (permutation4 j)) := by apply Matrix.ext; unfold raw21631step1 raw21631step0; decide +kernel
      have hl : raw21631step1Labels = raw21631step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21631step0 raw21631step0Labels permutation40 permutation4
    mixedMoment B raw21631step1 raw21631step1Labels = mixedMoment B raw21631step2 raw21631step2Labels := by
      have ha : raw21631step2 = -raw21631step1 := by apply Matrix.ext; change ∀ i j, raw21631step2 i j = -(raw21631step1 i j); unfold raw21631step2 raw21631step1; decide +kernel
      have hl : raw21631step2Labels = raw21631step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node706 node706Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
